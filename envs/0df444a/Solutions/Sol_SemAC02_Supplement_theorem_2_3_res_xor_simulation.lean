-- Prove2me | solution 1 for SemAC02.Supplement.theorem_2_3_res_xor_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T06:05:14.015384+00:00
-- url     : https://prove2.me/submissions/3d87d445-62e7-4eca-bbe3-1cf73a320c41

import Definitions.Def_SemAC02_Supplement_ResXor
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_IsSemPCRef

section
-- Inlined Solutions.ArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.ArithmeticCircuitBasics
end

section
-- Inlined Solutions.AffineBooleanForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.AffineBooleanForms

open ACirc ArithmeticCircuitBasics MvPolynomial

lemma zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def evalMap {V : Type} [Fintype V] (x : V → Bool) :
    (Option V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v none+∑ i, v (some i)*(if x i then 1 else 0)
  map_add' v w := by simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]; ring
  map_smul' a v := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_add,Finset.mul_sum,mul_assoc] <;> ring

def equationVector {V : Type} (e : LinEq V) : Option V → ZMod 2
  | none => e.2+1
  | some i => e.1 i

lemma vector_nonzero_iff {V : Type} [Fintype V] (e : LinEq V) (x : V → Bool) :
    evalMap x (equationVector e) ≠ 0 ↔ e.Sat x := by
  change e.2+1+(∑ i, e.1 i*(if x i then 1 else 0)) ≠ 0 ↔
    (∑ i, e.1 i*(if x i then 1 else 0)) = e.2
  let l := ∑ i, e.1 i*(if x i then (1 : ZMod 2) else 0)
  change e.2+1+l ≠ 0 ↔ l = e.2
  rw [show e.2+1+l = 1+(l+e.2) by ring,← CharTwo.add_eq_zero]
  rcases zero_or_one (l+e.2) with h | h
  · norm_num [h]
  · simp only [h,CharTwo.add_self_eq_zero,ne_eq,not_true_eq_false,one_ne_zero]

noncomputable def affineCircuit {V : Type} [Fintype V] (v : Option V → ZMod 2) : ACirc (ZMod 2) V :=
  .sum ((v none+1,.const 1)::(Finset.univ.toList.map (fun i => (v (some i),.var i))))

lemma cval_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (x : V → Bool) :
    cval (affineCircuit v) x = 1+evalMap x v := by
  rw [affineCircuit,cval_sum]
  simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def,cval,polyFn,toPoly,
    eval_C,eval_X,mul_one]
  rw [Finset.sum_map_toList]
  change v none+1+(∑ i, v (some i)*(if x i then 1 else 0)) =
    1+(v none+∑ i, v (some i)*(if x i then 1 else 0))
  ring

lemma affine_layer {V : Type} [Fintype V] (v : Option V → ZMod 2) :
    IsSumOf IsLeaf (affineCircuit v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · trivial
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    trivial

lemma subterms_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (c : ACirc (ZMod 2) V)
    (hc : c ∈ subterms (affineCircuit v)) :
    c = affineCircuit v ∨ c = .const 1 ∨ ∃ i : V, c = .var i := by
  classical
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simpa only [subterms,Finset.mem_singleton] using hc))
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      exact Or.inr (Or.inr ⟨i,by simpa only [subterms,Finset.mem_singleton] using hc⟩)

end SemAC02.Supplement.AffineBooleanForms
end

section
-- Inlined Solutions.LinearClauseCompression

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.LinearClauseCompression

open Module AffineBooleanForms

noncomputable def clauseSpace {V : Type} (D : LinClause V) :
    Submodule (ZMod 2) (Option V → ZMod 2) :=
  Submodule.span (ZMod 2) (equationVector '' {e | e ∈ D})

noncomputable def clauseBasis {V : Type} [Fintype V] (D : LinClause V) :
    Basis (Fin (finrank (ZMod 2) (clauseSpace D))) (ZMod 2) (clauseSpace D) :=
  Module.finBasis (ZMod 2) (clauseSpace D)

lemma basis_card_le {V : Type} [Fintype V] (D : LinClause V) :
    finrank (ZMod 2) (clauseSpace D) ≤ Fintype.card V+1 := by
  have h := Submodule.finrank_le (clauseSpace D)
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_option] using h

lemma vector_mem {V : Type} (D : LinClause V) (e : LinEq V) (he : e ∈ D) :
    equationVector e ∈ clauseSpace D := Submodule.subset_span ⟨e,he,rfl⟩

lemma basis_zero_iff {V : Type} [Fintype V] (D : LinClause V) (x : V → Bool) :
    (∀ i, evalMap x ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2) = 0) ↔
      ∀ e ∈ D, evalMap x (equationVector e) = 0 := by
  constructor
  · intro hi
    let E : clauseSpace D →ₗ[ZMod 2] ZMod 2 := (evalMap x).comp (clauseSpace D).subtype
    have hE : E = 0 := by
      apply (clauseBasis D).ext
      intro i
      exact hi i
    intro e he
    have hv := LinearMap.congr_fun hE ⟨equationVector e,vector_mem D e he⟩
    exact hv
  · intro he
    have hker : clauseSpace D ≤ (evalMap x).ker := by
      apply Submodule.span_le.mpr
      rintro v ⟨e,heD,rfl⟩
      exact he e heD
    intro i
    exact hker (clauseBasis D i).2

lemma not_all_zero_iff_sat {V : Type} [Fintype V] (D : LinClause V) (x : V → Bool) :
    (¬ ∀ e ∈ D, evalMap x (equationVector e) = 0) ↔ LinClause.Sat x D := by
  classical
  constructor
  · intro h
    push_neg at h
    obtain ⟨e,he,hne⟩ := h
    exact ⟨e,he,(vector_nonzero_iff e x).mp hne⟩
  · rintro ⟨e,he,hs⟩ hall
    exact (vector_nonzero_iff e x).mpr hs (hall e he)

end SemAC02.Supplement.LinearClauseCompression
end

section
-- Inlined Solutions.CompressedXorCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.CompressedXorCircuits

open Module ACirc ArithmeticCircuitBasics AffineBooleanForms LinearClauseCompression

noncomputable def lineProduct {V : Type} [Fintype V] (D : LinClause V) : ACirc (ZMod 2) V :=
  .prod (Finset.univ.toList.map (fun i => affineCircuit ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2)))

noncomputable def lineCircuit {V : Type} [Fintype V] (D : LinClause V) : ACirc (ZMod 2) V :=
  .sum [(1,lineProduct D)]

lemma one_add_zero_iff (a : ZMod 2) : 1+a = 0 ↔ a ≠ 0 := by
  rw [CharTwo.add_eq_zero]
  constructor
  · intro h ha
    exact one_ne_zero (h.trans ha)
  · intro h
    rcases zero_or_one a with ha | ha
    · exact (h ha).elim
    · exact ha.symm

lemma line_zero_iff {V : Type} [Fintype V] (D : LinClause V) (x : V → Bool) :
    cval (lineCircuit D) x = 0 ↔ LinClause.Sat x D := by
  classical
  rw [lineCircuit,cval_sum]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  rw [lineProduct,cval_prod]
  simp only [List.map_map,Function.comp_def,cval_affine,List.prod_eq_zero_iff,List.mem_map]
  have he : (∃ i : Fin (finrank (ZMod 2) (clauseSpace D)),
      1+evalMap x ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2) = 0) ↔
      ¬ ∀ i, evalMap x ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2) = 0 := by
    simp only [one_add_zero_iff,not_forall]
  simp only [Finset.mem_toList,Finset.mem_univ,true_and]
  rw [he,basis_zero_iff,not_all_zero_iff_sat]

lemma line_layer {V : Type} [Fintype V] (D : LinClause V) : IsSPS (lineCircuit D) := by
  intro q hq
  have hq' : q = (1,lineProduct D) := List.mem_singleton.mp hq
  subst q
  intro c hc
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
  exact affine_layer _

lemma topTerms_lineCircuit {V : Type} [Fintype V] (D : LinClause V) :
    topTerms (lineCircuit D) = [lineProduct D] := rfl

lemma subterms_lineCircuit {V : Type} [Fintype V] (D : LinClause V) (c : ACirc (ZMod 2) V)
    (hc : c ∈ subterms (lineCircuit D)) :
    c = lineCircuit D ∨ c = lineProduct D ∨
      (∃ i, c = affineCircuit ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2)) ∨
      c = .const 1 ∨ ∃ i : V, c = .var i := by
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · have hq' : q = (1,lineProduct D) := List.mem_singleton.mp hq
    subst q
    rcases (mem_subterms_prod c _).mp hc with he | ⟨q,hq,hc⟩
    · exact Or.inr (Or.inl he)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      rcases subterms_affine _ c hc with he | he | ⟨j,hj⟩
      · exact Or.inr (Or.inr (Or.inl ⟨i,he⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j,hj⟩)))

end SemAC02.Supplement.CompressedXorCircuits
end

section
-- Inlined Solutions.XorClauseSemantics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.XorClauseSemantics

open MvPolynomial AffineBooleanForms

lemma value_eq_of_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases zero_or_one a with rfl | rfl
  · exact (h.mp rfl).symm
  · rcases zero_or_one b with rfl | rfl
    · exact (one_ne_zero (h.mpr rfl)).elim
    · rfl

lemma literal_sat_iff {V : Type} [Fintype V] [DecidableEq V] (l : V × Bool) (x : V → Bool) :
    (litLinEq l).Sat x ↔ polyFn (litPolyF (F := ZMod 2) l) x = 0 := by
  classical
  obtain ⟨i,b⟩ := l
  have hsum : (∑ j, (Pi.single i (1 : ZMod 2) : V → ZMod 2) j*(if x j then 1 else 0)) =
      (if x i then (1 : ZMod 2) else 0) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Pi.single_apply,hji,Ne.symm hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change (∑ j, (Pi.single i (1 : ZMod 2) : V → ZMod 2) j*(if x j then 1 else 0)) =
    (if b then (1 : ZMod 2) else 0) ↔ _
  rw [hsum]
  cases b <;> cases hxi : x i <;> norm_num [polyFn,litPolyF,boolPt,hxi]

lemma clause_zero_iff {V : Type} [Fintype V] [DecidableEq V]
    (C : LiftSAParity.Clause V) (x : V → Bool) :
    polyFn (clausePolyF (F := ZMod 2) C) x = 0 ↔ LinClause.Sat x (C.toList.map litLinEq) := by
  classical
  simp only [polyFn,clausePolyF,map_prod]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨l,hl,hzero⟩
    refine ⟨litLinEq l,List.mem_map.mpr ⟨l,Finset.mem_toList.mpr hl,rfl⟩,?_⟩
    exact (literal_sat_iff l x).mpr hzero
  · rintro ⟨e,he,hs⟩
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp he
    exact ⟨l,Finset.mem_toList.mp hl,(literal_sat_iff l x).mp hs⟩

lemma sat_perm {V : Type} [Fintype V] {D E : LinClause V} (h : D.Perm E) (x : V → Bool) :
    LinClause.Sat x D ↔ LinClause.Sat x E := by
  simp only [LinClause.Sat,h.mem_iff]

lemma input_value {V : Type} [Fintype V] [DecidableEq V] (D : LinClause V)
    (C : LiftSAParity.Clause V) (h : D.Perm (C.toList.map litLinEq)) (x : V → Bool) :
    cval (CompressedXorCircuits.lineCircuit D) x = polyFn (clausePolyF C) x := by
  apply value_eq_of_zero_iff
  rw [CompressedXorCircuits.line_zero_iff,clause_zero_iff]
  exact sat_perm h x

end SemAC02.Supplement.XorClauseSemantics
end

section
-- Inlined Solutions.XorSemanticSimulation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.XorSemanticSimulation

open ACirc CompressedXorCircuits XorClauseSemantics AffineBooleanForms

theorem simulate {V : Type} [Fintype V] [DecidableEq V] (φ : LiftSAParity.CNF V)
    (π : List (LinClause V)) (hπ : IsSemResXorRef φ π) :
    IsSemPCRef IsSPS Set.univ (clauseAx (φ : Set (LiftSAParity.Clause V))) (π.map lineCircuit) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro c hc
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hc
    exact line_layer D
  · intro k hk
    have hkπ : k < π.length := by simpa only [List.length_map] using hk
    rcases hπ.1 k hkπ with ⟨C,hC,hperm⟩ | ⟨i,j,hi,hj,hinf⟩
    · refine Or.inl ⟨polyFn (clausePolyF C),⟨C,hC,rfl⟩,?_⟩
      intro x hx
      simpa only [List.getElem_map] using input_value π[k] C hperm x
    · refine Or.inr (Or.inr ⟨i,j,hi,hj,?_⟩)
      intro x hx h₁ h₂
      have h₁' : LinClause.Sat x π[i] := (line_zero_iff π[i] x).mp (by
        simpa only [List.getElem_map] using h₁)
      have h₂' : LinClause.Sat x π[j] := (line_zero_iff π[j] x).mp (by
        simpa only [List.getElem_map] using h₂)
      simpa only [List.getElem_map] using (line_zero_iff π[k] x).mpr (hinf x h₁' h₂')
  · refine ⟨lineCircuit [],?_,?_⟩
    · rw [List.getLast?_map,hπ.2]
      rfl
    · intro x hx
      rcases zero_or_one (cval (lineCircuit ([] : LinClause V)) x) with hzero | hone
      · have hh := (line_zero_iff ([] : LinClause V) x).mp hzero
        simpa only [LinClause.Sat,List.not_mem_nil,false_and,exists_false] using hh
      · exact hone

end SemAC02.Supplement.XorSemanticSimulation
end

section
-- Inlined Solutions.ArithmeticProofCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticProofCounts

open ACirc

lemma csize_cons {F V : Type} (c : ACirc F V) (π : List (ACirc F V)) :
    csize (c::π) ≤ (subterms c).card+csize π := by
  classical
  unfold csize
  rw [List.toFinset_cons,Finset.biUnion_insert]
  exact Finset.card_union_le _ _

theorem csize_map_le {F V I : Type} (π : List I) (f : I → ACirc F V) (B : ℕ)
    (hf : ∀ i ∈ π, (subterms (f i)).card ≤ B) : csize (π.map f) ≤ π.length*B := by
  induction π with
  | nil => simp [csize]
  | cons i π ih =>
    have h := (csize_cons (f i) (π.map f)).trans (Nat.add_le_add
      (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj]))))
    simpa only [List.map_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

theorem topS_le_topOcc {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ topOcc π := by
  classical
  let ts := π.flatMap topTerms
  let G : Finset (Ω → F) := ts.toFinset.image (fun t => fun x : Ω => cval t x.1)
  have hsub : {g : Ω → F | g ≠ 0 ∧ ∃ c ∈ π, ∃ t ∈ topTerms c, g = fun x => cval t x.1} ⊆
      (↑G : Set (Ω → F)) := by
    rintro g ⟨hg,c,hc,t,ht,rfl⟩
    exact Finset.mem_image.mpr ⟨t,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,ht⟩),rfl⟩
  calc
    _ ≤ (↑G : Set (Ω → F)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet G)
    _ = G.card := Set.ncard_coe_finset _
    _ ≤ ts.toFinset.card := Finset.card_image_le
    _ ≤ ts.length := List.toFinset_card_le ts
    _ = _ := by simp only [ts,List.length_flatMap,topOcc]

end SemAC02.Supplement.ArithmeticProofCounts
end

section
-- Inlined Solutions.XorCircuitSize

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.XorCircuitSize

open Module ACirc AffineBooleanForms LinearClauseCompression CompressedXorCircuits

theorem line_size {V : Type} [Fintype V] (D : LinClause V) :
    (subterms (lineCircuit D)).card ≤ 2*Fintype.card V+4 := by
  classical
  let m := finrank (ZMod 2) (clauseSpace D)
  let Gₐ : Finset (ACirc (ZMod 2) V) := Finset.univ.image
    (fun i : Fin m => affineCircuit ((clauseBasis D i : clauseSpace D) : Option V → ZMod 2))
  let Gᵥ : Finset (ACirc (ZMod 2) V) := Finset.univ.image ACirc.var
  let S := insert (lineCircuit D) (insert (lineProduct D) (insert (.const 1) (Gₐ ∪ Gᵥ)))
  have hsub : subterms (lineCircuit D) ⊆ S := by
    intro c hc
    rcases subterms_lineCircuit D c hc with he | he | ⟨i,he⟩ | he | ⟨i,he⟩
    · simp only [S,Finset.mem_insert,Finset.mem_union]
      aesop
    · simp only [S,Finset.mem_insert,Finset.mem_union]
      aesop
    · have hm : c ∈ Gₐ := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
      simp only [S,Finset.mem_insert,Finset.mem_union]
      aesop
    · simp only [S,Finset.mem_insert,Finset.mem_union]
      aesop
    · have hm : c ∈ Gᵥ := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
      simp only [S,Finset.mem_insert,Finset.mem_union]
      aesop
  have hGₐ : Gₐ.card ≤ m := by
    exact Finset.card_image_le.trans_eq (by simp)
  have hGᵥ : Gᵥ.card ≤ Fintype.card V := by
    exact Finset.card_image_le.trans_eq (by simp)
  have hm : m ≤ Fintype.card V+1 := basis_card_le D
  have hcard : S.card ≤ Gₐ.card+Gᵥ.card+3 := by
    have h₀ := Finset.card_union_le Gₐ Gᵥ
    have h₁ := Finset.card_insert_le (.const (F := ZMod 2) (σ := V) 1) (Gₐ ∪ Gᵥ)
    have h₂ := Finset.card_insert_le (lineProduct D) (insert (.const 1) (Gₐ ∪ Gᵥ))
    have h₃ := Finset.card_insert_le (lineCircuit D) (insert (lineProduct D) (insert (.const 1) (Gₐ ∪ Gᵥ)))
    dsimp only [S]
    omega
  exact (Finset.card_le_card hsub).trans (by omega)

theorem size_bound {n : ℕ} (hn : 1 ≤ n) (π : List (LinClause (Fin n))) :
    csize (π.map lineCircuit) ≤ 6*n*π.length := by
  have hb : ∀ D ∈ π, (subterms (lineCircuit D)).card ≤ 6*n := by
    intro D hD
    have h := line_size D
    simp only [Fintype.card_fin] at h
    omega
  have h := ArithmeticProofCounts.csize_map_le π lineCircuit (6*n) hb
  simpa only [Nat.mul_comm π.length] using h

theorem topS_bound {V : Type} [Fintype V] (Ω : Set (V → Bool)) (π : List (LinClause V)) :
    topS Ω (π.map lineCircuit) ≤ π.length := by
  apply (ArithmeticProofCounts.topS_le_topOcc Ω _).trans_eq
  simp [topOcc,List.map_map,Function.comp_def,topTerms_lineCircuit]

end SemAC02.Supplement.XorCircuitSize
end

section
-- Inlined Solutions.ResXorSimulation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ResXorSimulation

open ACirc CompressedXorCircuits

theorem simulation :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ (φ : LiftSAParity.CNF (Fin n))
      (π : List (LinClause (Fin n))), IsSemResXorRef φ π →
      ∃ π' : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        topS Set.univ π' ≤ π.length ∧ (csize π' : ℝ) ≤ K*n*π.length := by
  refine ⟨6,?_⟩
  intro n hn φ π hπ
  refine ⟨π.map lineCircuit,XorSemanticSimulation.simulate φ π hπ,
    XorCircuitSize.topS_bound Set.univ π,?_⟩
  exact_mod_cast XorCircuitSize.size_bound hn π

end SemAC02.Supplement.ResXorSimulation
end

open SemAC02.Supplement SemAC02.Supplement.ACirc

theorem solution :
    ∃ K : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (φ : LiftSAParity.CNF (Fin n))
      (π : List (LinClause (Fin n))), IsSemResXorRef φ π →
      ∃ π' : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        topS Set.univ π' ≤ π.length ∧
        (csize π' : ℝ) ≤ K * n * π.length  := by
  exact SemAC02.Supplement.ResXorSimulation.simulation
