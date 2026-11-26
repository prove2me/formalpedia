-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_11_combinatorial
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:18:41.903847+00:00
-- url     : https://prove2.me/submissions/6dbb9ff0-3175-4e24-8904-6b74f9fce493

/- Cut-edge, submodularity, and attainment lemmas adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Theorems.Thm_SingleExpBisect_Main_lemma_2_1_combinatorial
import Definitions.Def_SingleExpBisect_Main_Graphs

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

private def edgeWithRoot {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (u v : Fin (n+1)) : Prop :=
  Fin.lastCases (Fin.lastCases False (fun j => j ∈ B) v)
    (fun i => Fin.lastCases (i ∈ B) (fun j => G.Adj i j) v) u

private def augment {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : SimpleGraph (Fin (n+1)) where
  Adj := edgeWithRoot G B
  symm := ⟨by
    intro u v h
    induction u using Fin.lastCases <;> induction v using Fin.lastCases <;>
      simp [edgeWithRoot] at * <;> first | assumption | exact h.symm⟩
  loopless := ⟨by intro u; induction u using Fin.lastCases <;> simp [edgeWithRoot]⟩

private def liftSet {n : ℕ} (A : Finset (Fin n)) := A.map Fin.castSuccEmb

private lemma mem_lift {n : ℕ} (A : Finset (Fin n)) (a : Fin n) :
    a.castSucc ∈ liftSet A ↔ a ∈ A := Finset.mem_map' Fin.castSuccEmb

private lemma last_out {n : ℕ} (A : Finset (Fin n)) : Fin.last n ∉ liftSet A := by
  rintro h; obtain ⟨u,_,he⟩ := Finset.mem_map.mp h; exact u.castSucc_ne_last he

private def oldE {n : ℕ} : Sym2 (Fin n) ↪ Sym2 (Fin (n+1)) := Fin.castSuccEmb.sym2Map

private def spoke {n : ℕ} : Fin n ↪ Sym2 (Fin (n+1)) := Fin.castSuccEmb.trans (Sym2.mkEmbedding (Fin.last n))

private lemma spoke_out {n : ℕ} (u : Fin n) (e : Sym2 (Fin n)) : spoke u ≠ oldE e := by
  induction e using Sym2.ind with
  | _ a b =>
    change s(Fin.last n,u.castSucc) ≠ s(a.castSucc,b.castSucc)
    intro eq; rcases Sym2.eq_iff.mp eq with ⟨h,_⟩ | ⟨h,_⟩
    · exact a.castSucc_ne_last h.symm
    · exact b.castSucc_ne_last h.symm

private lemma aug_cut {n : ℕ} (G : SimpleGraph (Fin n)) (B A : Finset (Fin n)) :
    cutSize (augment G B) (liftSet A) = cutSize G A + (A ∩ B).card := by
  classical
  let E := (cutEdges G A).map oldE
  let F := (A ∩ B).map spoke
  have dj : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    rintro e hE hF
    obtain ⟨i,_,he⟩ := Finset.mem_map.mp hE
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hF
    exact spoke_out j i (hj.trans he.symm)
  have eq : cutEdges (augment G B) (liftSet A) = E ∪ F := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      have sp (u : Fin n) : s(Fin.last n,u.castSucc) ∈ E ∪ F ↔ u ∈ A ∩ B := by
        change spoke u ∈ E ∪ F ↔ _
        have hh : spoke u ∉ E := fun h => by
          obtain ⟨q,_,hq⟩ := Finset.mem_map.mp h; exact spoke_out u q hq.symm
        simp only [Finset.mem_union,hh,false_or,F,Finset.mem_map']
      have oe (u v : Fin n) : s(u.castSucc,v.castSucc) ∈ E ∪ F ↔ s(u,v) ∈ cutEdges G A := by
        change oldE s(u,v) ∈ E ∪ F ↔ _
        have hh : oldE s(u,v) ∉ F := fun h => by
          obtain ⟨q,_,hq⟩ := Finset.mem_map.mp h; exact spoke_out q _ hq
        simp only [Finset.mem_union,hh,or_false,E,Finset.mem_map']
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last =>
          have h0 : s(Fin.last n,Fin.last n) ∉ E := by
            rintro h; obtain ⟨q,_,hq⟩ := Finset.mem_map.mp h
            induction q using Sym2.ind with
            | _ u v =>
              change s(u.castSucc,v.castSucc) = s(Fin.last n,Fin.last n) at hq
              rcases Sym2.eq_iff.mp hq with ⟨h,_⟩ | ⟨h,_⟩ <;> exact u.castSucc_ne_last h
          have h1 : s(Fin.last n,Fin.last n) ∉ F := by
            rintro h; obtain ⟨q,_,hq⟩ := Finset.mem_map.mp h
            change s(Fin.last n,q.castSucc) = s(Fin.last n,Fin.last n) at hq
            rcases Sym2.eq_iff.mp hq with ⟨_,h⟩ | ⟨_,h⟩ <;> exact q.castSucc_ne_last h
          simp [mem_cutEdges_mk,h0,h1]
        | cast u => rw [sp,mem_cutEdges_mk]; simp [augment,edgeWithRoot,last_out,mem_lift,and_comm]
      | cast u =>
        induction b using Fin.lastCases with
        | last => rw [Sym2.eq_swap,sp,mem_cutEdges_mk];simp [augment,edgeWithRoot,last_out,mem_lift,and_comm]
        | cast v => rw [oe,mem_cutEdges_mk,mem_cutEdges_mk];simp [augment,edgeWithRoot,mem_lift]
  unfold cutSize; rw [eq,Finset.card_union_of_disjoint dj]; simp [E,F]

private lemma conn_lift {n : ℕ} (G : SimpleGraph (Fin n)) (B A : Finset (Fin n))
    (hc : (G.induce (A : Set _)).Connected) : ((augment G B).induce (liftSet A : Set _)).Connected := by
  let f : G.induce (A : Set _) →g (augment G B).induce (liftSet A : Set _) :=
    ⟨fun u => ⟨u.val.castSucc,(mem_lift A u.val).mpr u.property⟩,fun {u v} h => by
      change edgeWithRoot G B u.val.castSucc v.val.castSucc
      simpa [edgeWithRoot] using h⟩
  apply hc.map f
  intro v
  obtain ⟨u,hu,he⟩ := Finset.mem_map.mp v.property
  exact ⟨⟨u,hu⟩,Subtype.ext he⟩

private def strip {n : ℕ} (D : Finset (Fin (n+1))) := Finset.univ.filter fun v : Fin n => v.castSucc ∈ D

private lemma lift_strip {n : ℕ} (D : Finset (Fin (n+1))) (hd : Fin.last n ∉ D) :
    liftSet (strip D) = D := by
  ext i; induction i using Fin.lastCases with
  | last => simp [last_out,hd]
  | cast u => simp [mem_lift,strip]

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)) :
    ∃ L : Finset (Finset (Fin n)),
      (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2*k) ∧
      (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧
      L.card ≤ 1 + B.card * 2^(9*k) ∧
      ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set (Fin n))).Connected) →
        cutSize G A ≤ k → (A ∩ B).card ≤ 2*k → A ∩ B ∈ L := by
  classical
  let H := augment G B
  let source := fun v : Fin n => ({v.castSucc} : Finset (Fin (n+1)))
  let T := ({Fin.last n} : Finset (Fin (n+1)))
  let fam := fun v : Fin n => (Finset.univ : Finset (Finset (Fin (n+1)))).filter
      (fun D => IsImportantConnCut H (source v) T D ∧ cutSize H D ≤ 3*k)
  have memF (v : Fin n) (D : Finset (Fin (n+1))) :
      D ∈ fam v ↔ IsImportantConnCut H (source v) T D ∧ cutSize H D ≤ 3*k := by simp [fam]
  have src (v : Fin n) : (H.induce (source v : Set _)).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨v.castSucc,Finset.mem_singleton_self _⟩,?_⟩
    rintro ⟨x,hx⟩
    have e : x = v.castSucc := Finset.mem_singleton.mp hx
    subst x; exact .refl _
  have dj (v : Fin n) : Disjoint (source v) T := by
    simpa [source,T] using v.castSucc_ne_last
  let group := fun D : Finset (Fin (n+1)) => ((strip D ∩ B).powerset.filter fun P => P.card ≤ 2*k)
  let candidates := B.biUnion fam
  let L := insert ∅ (candidates.biUnion group)
  have cand (D : Finset (Fin (n+1))) : D ∈ candidates ↔ ∃ v ∈ B, D ∈ fam v := Finset.mem_biUnion
  have groups (P : Finset (Fin n)) (D : Finset (Fin (n+1))) :
      P ∈ group D ↔ P ⊆ strip D ∩ B ∧ P.card ≤ 2*k := by simp only [group,Finset.mem_filter,Finset.mem_powerset]
  have hL (P : Finset (Fin n)) : P ∈ L ↔ P = ∅ ∨ ∃ D ∈ candidates, P ∈ group D := by simp [L]
  have cardF : candidates.card ≤ B.card * 4^(3*k) :=
    Finset.card_biUnion_le_card_mul _ _ _ fun v _ =>
      (lemma_2_1_combinatorial (n+1) H (source v) T (dj v) (src v)).2 (3*k)
  have cardG : (candidates.biUnion group).card ≤ candidates.card * 2^(3*k) := by
    apply Finset.card_biUnion_le_card_mul
    intro D hD
    obtain ⟨v,hv,hf⟩ := (cand D).mp hD
    obtain ⟨hi,hk⟩ := (memF v D).mp hf
    have hd : Fin.last n ∉ D := fun h => Finset.disjoint_left.mp hi.1.2.1 h (Finset.mem_singleton_self _)
    have eq := aug_cut G B (strip D)
    rw [lift_strip D hd] at eq
    change cutSize H D = _ at eq
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((Finset.card_powerset _).le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  refine ⟨L,?_,?_,?_,?_⟩
  · intro D hD
    obtain rfl | ⟨E,hE,hDE⟩ := (hL D).mp hD
    · simp
    · obtain ⟨h,hc⟩ := (groups D E).mp hDE
      exact ⟨h.trans Finset.inter_subset_right,hc⟩
  · intro D hD D' h'
    apply (hL D').mpr
    obtain rfl | ⟨E,hE,hDE⟩ := (hL D).mp hD
    · exact Or.inl (Finset.subset_empty.mp h')
    · have h := (groups D E).mp hDE
      exact Or.inr ⟨E,hE,(groups D' E).mpr ⟨h'.trans h.1,(Finset.card_le_card h').trans h.2⟩⟩
  · calc
      L.card ≤ (candidates.biUnion group).card + 1 := Finset.card_insert_le _ _
      _ ≤ B.card * 4^(3*k) * 2^(3*k) + 1 := Nat.add_le_add_right
        (cardG.trans (Nat.mul_le_mul_right _ cardF)) _
      _ = _ := by
        rw [show 4 = 2^2 by decide,←pow_mul,mul_assoc B.card,←pow_add,show 2*(3*k)+3*k=9*k by omega]
        omega
  · intro A hconn hcost hsize
    by_cases he : A ∩ B = ∅
    · exact (hL _).mpr (Or.inl he)
    have ha : (G.induce (A : Set _)).Connected := hconn.resolve_left (fun h => he (by simp [h]))
    obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hc : IsConnCut H (source v) T (liftSet A) := by
      refine ⟨Finset.singleton_subset_iff.mpr ((mem_lift A v).mpr (Finset.mem_inter.mp hv).1),?_,conn_lift G B A ha⟩
      simpa [T] using last_out A
    obtain ⟨D,hi,hAD,hcut⟩ := (lemma_2_1_combinatorial (n+1) H (source v) T (dj v) (src v)).1 _ hc
    apply (hL _).mpr; apply Or.inr
    refine ⟨D,(cand D).mpr ⟨v,(Finset.mem_inter.mp hv).2,(memF v D).mpr ⟨hi,?_⟩⟩,(groups _ D).mpr ⟨?_,hsize⟩⟩
    · change cutSize H D ≤ 3*k
      have hh : cutSize H (liftSet A) = _ := aug_cut G B A
      omega
    · intro x hx
      obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAD ((mem_lift A x).mpr ha)⟩,hb⟩
