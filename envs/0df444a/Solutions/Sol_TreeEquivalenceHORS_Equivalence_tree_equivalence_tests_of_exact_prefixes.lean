-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.tree_equivalence_tests_of_exact_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:11:22.733115+00:00
-- url     : https://prove2.me/submissions/2d8c3a18-7cc8-4cc2-8ca8-f261f0468dd2

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_syntax_and_code_tests
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_trees_equal_iff_prefixes
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_productive_iff_prefixes_no_bottom

namespace TreeEquivalenceHORS.Equivalence



private def stat (k : ℕ) (G H : HORS) : Prop := ValidPair G H ∧ (0 < k → G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ H.order ≤ 4) ∧ (k = 3 → G.Safe ∧ H.Safe)

private def resultAt (k n d : ℕ) (G H : HORS) : Prop :=
  Encodable.decode n = some (G,H) ∧ stat k G H ∧
    G.Pref (.nt G.start) d = H.Pref (.nt H.start) d ∧
    (2 ≤ k → (∀ p ∈ G.Pref (.nt G.start) d, p.2 ≠ .bot) ∧
             (∀ p ∈ H.Pref (.nt H.start) d, p.2 ≠ .bot))

private def allDepths (k n : ℕ) : Prop := ∀ d, ∃ G H, resultAt k n d G H

private theorem allDepths_iff (k n : ℕ) : allDepths k n ↔ ∃ G H, Encodable.decode n = some (G,H) ∧
    stat k G H ∧ G.BT = H.BT ∧ (2 ≤ k → G.Prod ∧ H.Prod) := by
  have ty (G : HORS) (hg : G.Valid) : G.typeOf [] (.nt G.start) = some .o := by
    simp only [HORS.Valid,HORS.valid,Bool.and_eq_true,beq_iff_eq] at hg
    exact hg.1.2
  constructor
  · intro h
    obtain ⟨G,H,dec,st,_⟩ := h 0
    have vd := st.1
    have all' (d : ℕ) : resultAt k n d G H := by
      obtain ⟨X,Y,hh⟩ := h d
      cases Option.some.inj (dec.symm.trans hh.1)
      exact hh
    refine ⟨G,H,dec,st,?_,?_⟩
    · apply (trees_equal_iff_prefixes G H vd.1 vd.2.1 vd.2.2 _ _ (ty _ vd.1) (ty _ vd.2.1)).mpr
      intro d
      exact (all' d).2.2.1
    · intro hk
      constructor
      · apply (productive_iff_prefixes_no_bottom G vd.1 _ (ty _ vd.1)).mpr
        exact fun d => ((all' d).2.2.2 hk).1
      · apply (productive_iff_prefixes_no_bottom H vd.2.1 _ (ty _ vd.2.1)).mpr
        exact fun d => ((all' d).2.2.2 hk).2
  · rintro ⟨G,H,dec,st,tree,prod⟩ d
    have vd := st.1
    refine ⟨G,H,dec,st,(trees_equal_iff_prefixes G H vd.1 vd.2.1 vd.2.2 _ _ (ty _ vd.1) (ty _ vd.2.1)).mp tree d,?_⟩
    intro hk
    exact ⟨(productive_iff_prefixes_no_bottom G vd.1 _ (ty _ vd.1)).mp (prod hk).1 d,
      (productive_iff_prefixes_no_bottom H vd.2.1 _ (ty _ vd.2.1)).mp (prod hk).2 d⟩

private theorem langs_at (n : ℕ) :
    (EqHORS n ↔ allDepths 0 n) ∧ (Eq4Sigma2 n ↔ allDepths 1 n) ∧
    (Eq4Sigma2Prod n ↔ allDepths 2 n) ∧ (Eq4Sigma2SafeProd n ↔ allDepths 3 n) := by
  simp [allDepths_iff, EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd, stat,
    and_assoc, and_left_comm, and_comm]

private def allLabels (n : ℕ) : Prop :=
    ∀ p ∈ (Encodable.decode n : Option (List (ℕ × ℕ))).getD [], p.2 ≠ Encodable.encode Lab.bot

private theorem labels_pr : PrimrecPred allLabels :=
  (PrimrecPred.forall_mem_list (Primrec.eq.comp Primrec.snd (Primrec.const (Encodable.encode Lab.bot))).not).comp
    (Primrec.option_getD.comp Primrec.decode (Primrec.const []))

private theorem labels_correct (ps : List (List ℕ × Lab)) :
    allLabels (Encodable.encode ps) ↔ ∀ p ∈ ps, p.2 ≠ .bot := by
  let ps' := ps.map fun (w,l) => (Encodable.encode w, Encodable.encode l)
  have e : Encodable.encode ps' = Encodable.encode ps := by
    change Encodable.encode (ps.map _) = _
    induction ps with
    | nil => rfl
    | cons p ps ih => rcases p with ⟨w,l⟩; simp_all [Encodable.encode_prod_val]
  unfold allLabels
  rw [←e, Encodable.encodek]
  simp only [Option.getD_some]
  constructor
  · intro h p hp eq
    exact h _ (List.mem_map_of_mem (f := fun (w,l) => (Encodable.encode w, Encodable.encode l)) hp) (congrArg Encodable.encode eq)
  · intro h p hp eq
    obtain ⟨⟨w,l⟩,hl,rfl⟩ := List.mem_map.mp hp
    exact h (w,l) hl (Encodable.encode_injective eq)

private theorem depth_tests_from_prefix_algorithm
    (q : ℕ → ℕ → Bool) (hq : Computable₂ q)
    (qspec : ∀ k n, q k n = true ↔ ∃ G H, Encodable.decode n = some (G,H) ∧ stat k G H)
    (start : ℕ → ℕ) (cs : Computable start)
    (st : ∀ G : HORS, start (Encodable.encode G) = Encodable.encode (Tm.nt G.start))
    (pairCode : ∀ n (G H : HORS), Encodable.decode n = some (G,H) → Encodable.encode (G,H) = n)
    (pref : ℕ × ℕ × ℕ → ℕ) (cp : Computable pref)
    (cspec : ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
      pref (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d)) :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true := by
  classical
  let read (x d : ℕ) := pref (x,start x,d)
  have rc : Computable₂ read := (cp.comp (Computable.fst.pair ((cs.comp Computable.fst).pair Computable.snd))).to₂
  have read_ok (G : HORS) (vg : G.Valid) (d : ℕ) :
      read (Encodable.encode G) d = Encodable.encode (G.Pref (.nt G.start) d) := by
    change pref _ = _
    rw [st]
    apply cspec _ _ _ vg
    simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, beq_iff_eq] at vg
    exact vg.1.2
  let test (k n d : ℕ) : Bool := q k n && (read n.unpair.1 d == read n.unpair.2 d) &&
    (decide (k < 2) || (decide (allLabels (read n.unpair.1 d)) && decide (allLabels (read n.unpair.2 d))))
  have tc (k : ℕ) : Computable₂ (test k) := by
    have l := rc.comp ((Computable.fst.comp Computable.unpair).comp Computable.fst) (Computable.snd (α := ℕ) (β := ℕ))
    have r := rc.comp ((Computable.snd.comp Computable.unpair).comp Computable.fst) (Computable.snd (α := ℕ) (β := ℕ))
    exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp (hq.comp (Computable.const k) Computable.fst)
      (Primrec.beq.to_comp.comp l r)) (Primrec.or.to_comp.comp (Computable.const _)
        (Primrec.and.to_comp.comp (labels_pr.decide.to_comp.comp l) (labels_pr.decide.to_comp.comp r)))).to₂
  have spec (k n d : ℕ) : test k n d = true ↔ ∃ G H, resultAt k n d G H := by
    by_cases qs : q k n = true
    · obtain ⟨G,H,dec,hst⟩ := (qspec k n).mp qs
      obtain rfl := pairCode n G H dec
      rw [Encodable.encode_prod_val] at qs
      simp only [test, Encodable.encode_prod_val, qs, Nat.unpair_pair, read_ok G hst.1.1,
        read_ok H hst.1.2.1, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq, true_and, labels_correct, Encodable.encode_injective.eq_iff]
      constructor
      · rintro ⟨e,h⟩
        exact ⟨G,H,dec,hst,e,fun hk => h.resolve_left (Nat.not_lt.mpr hk)⟩
      · rintro ⟨X,Y,hx⟩
        cases Option.some.inj (dec.symm.trans hx.1)
        exact ⟨hx.2.2.1, (lt_or_ge k 2).imp_right hx.2.2.2⟩
    · simp [test, qs]
      rintro G H hg
      exact qs ((qspec k n).mpr ⟨G,H,hg.1,hg.2.1⟩)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  have supply (P : ℕ → Prop) (k : ℕ) (hp : ∀ n, P n ↔ allDepths k n) :
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true :=
    ⟨test k, tc k, fun n => (hp n).trans <| forall_congr' (fun d => (spec k n d).symm)⟩
  rcases hP with rfl | rfl | rfl | rfl
  · exact supply _ 0 (fun n => (langs_at n).1)
  · exact supply _ 1 (fun n => (langs_at n).2.1)
  · exact supply _ 2 (fun n => (langs_at n).2.2.1)
  · exact supply _ 3 (fun n => (langs_at n).2.2.2)


private theorem proved_here
    (pf : ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d)) :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true := by
  obtain ⟨⟨q,hq,qs⟩,⟨s,hs,ss⟩,pairCode⟩ := syntax_and_code_tests
  obtain ⟨f,hf,fs⟩ := pf
  exact depth_tests_from_prefix_algorithm q hq qs s hs ss pairCode f hf fs

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution
    (pf : ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d)) :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true := proved_here pf
