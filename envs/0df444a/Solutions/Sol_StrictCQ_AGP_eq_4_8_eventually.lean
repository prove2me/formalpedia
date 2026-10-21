-- Prove2me | solution 1 for StrictCQ.AGP.eq_4_8_eventually
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:21:52.361381+00:00
-- url     : https://prove2.me/submissions/cf80c86c-0308-47f4-b3dc-43e0241f54c7

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

set_option autoImplicit false
open Filter Topology InnerProductSpace
open StrictCQ.AGP

section ProjLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_le_of_min {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (hmin : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖) : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0 := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have : ‖z - p‖ = ⨅ w : S, ‖z - (w : E)‖ := by
    have : Nonempty S := ⟨⟨p, hp⟩⟩
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le hb ⟨p, hp⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hcv hp).1 this

lemma min_of_inner_le {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (h : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0) : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖ := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).2 h
  intro w hw
  rw [this]
  exact ciInf_le hb ⟨w, hw⟩

lemma proj_nonexp {S : Set E} (hcv : Convex ℝ S) {z z' y y' : E} (hy : y ∈ S) (hy' : y' ∈ S)
    (h1 : ∀ w ∈ S, ‖z - y‖ ≤ ‖z - w‖) (h2 : ∀ w ∈ S, ‖z' - y'‖ ≤ ‖z' - w‖) :
    ‖y - y'‖ ≤ ‖z - z'‖ := by
  have a1 := inner_le_of_min hcv hy h1 y' hy'
  have a2 := inner_le_of_min hcv hy' h2 y hy
  have key : ‖y - y'‖ ^ 2 ≤ inner ℝ (z - z') (y - y') := by
    have e1 : inner ℝ (z - y) (y' - y) = - inner ℝ (z - y) (y - y') := by
      rw [← inner_neg_right]; congr 1; abel
    have e2 : inner ℝ (z' - y') (y - y') = inner ℝ (z' - y') (y - y') := rfl
    have e3 : inner ℝ (z - z') (y - y') = inner ℝ (z - y) (y - y') - inner ℝ (z' - y') (y - y')
        + inner ℝ (y - y') (y - y') := by
      rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
    rw [e3, real_inner_self_eq_norm_sq]
    linarith
  have key2 : inner ℝ (z - z') (y - y') ≤ ‖z - z'‖ * ‖y - y'‖ := real_inner_le_norm _ _
  by_cases h0 : ‖y - y'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y - y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
end ProjLib

section FarkasLib
open Classical

variable {n : ℕ} {ι : Type*}

def conicSet (s : Finset ι) (v : ι → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ μ : ι → ℝ, (∀ i ∈ s, 0 ≤ μ i) ∧ x = ∑ i ∈ s, μ i • v i}

lemma conicSet_zero (s : Finset ι) (v : ι → EuclideanSpace ℝ (Fin n)) : 0 ∈ conicSet s v :=
  ⟨fun _ => 0, fun _ _ => le_rfl, by simp⟩

lemma conicSet_add {s : Finset ι} {v : ι → EuclideanSpace ℝ (Fin n)} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ conicSet s v) (hy : y ∈ conicSet s v) : x + y ∈ conicSet s v := by
  obtain ⟨μ, hμ, rfl⟩ := hx
  obtain ⟨ν, hν, rfl⟩ := hy
  refine ⟨fun i => μ i + ν i, fun i hi => add_nonneg (hμ i hi) (hν i hi), ?_⟩
  simp [add_smul, Finset.sum_add_distrib]

lemma conicSet_smul {s : Finset ι} {v : ι → EuclideanSpace ℝ (Fin n)} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ conicSet s v) {c : ℝ} (hc : 0 ≤ c) : c • x ∈ conicSet s v := by
  obtain ⟨μ, hμ, rfl⟩ := hx
  refine ⟨fun i => c * μ i, fun i hi => mul_nonneg hc (hμ i hi), ?_⟩
  simp [Finset.smul_sum, mul_smul]

lemma conicSet_convex (s : Finset ι) (v : ι → EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (conicSet s v) := by
  intro x hx y hy a b ha hb _
  exact conicSet_add (conicSet_smul hx ha) (conicSet_smul hy hb)

lemma conicSet_insert {s : Finset ι} {a : ι} (ha : a ∉ s) (v : ι → EuclideanSpace ℝ (Fin n)) :
    conicSet (insert a s) v =
      {x | ∃ y ∈ conicSet s v, ∃ t : ℝ, 0 ≤ t ∧ x = y + t • v a} := by
  ext x
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨∑ i ∈ s, μ i • v i, ⟨μ, fun i hi => hμ i (Finset.mem_insert_of_mem hi), rfl⟩,
      μ a, hμ a (Finset.mem_insert_self _ _), ?_⟩
    rw [Finset.sum_insert ha]; abel
  · rintro ⟨_, ⟨μ, hμ, rfl⟩, t, ht, rfl⟩
    refine ⟨Function.update μ a t, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · subst hia; simpa using ht
      · rw [Function.update_of_ne hia]
        exact hμ i ((Finset.mem_insert.1 hi).resolve_left hia)
    · rw [Finset.sum_insert ha, Function.update_self, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (by rintro rfl; exact ha hi)]

lemma conicSet_isClosed (s : Finset ι) : ∀ v : ι → EuclideanSpace ℝ (Fin n),
    IsClosed (conicSet s v) := by
  induction s using Finset.induction_on with
  | empty =>
    intro v
    have : conicSet (∅ : Finset ι) v = {0} := by
      ext x
      constructor
      · rintro ⟨μ, _, rfl⟩; simp
      · intro hx; rw [Set.mem_singleton_iff.1 hx]; exact conicSet_zero _ _
    rw [this]; exact isClosed_singleton
  | insert a s ha ih =>
    intro v
    have hK := conicSet_insert ha v
    have hK' := ih v
    set K' := conicSet s v with hK'def
    set u := v a with hu
    by_cases hneg : -u ∈ K'
    · -- Case 2: the cone contains the line through u
      by_cases hu0 : u = 0
      · have : conicSet (insert a s) v = K' := by
          rw [hK]; ext x
          constructor
          · rintro ⟨y, hy, t, _, rfl⟩; simpa [hu0] using hy
          · intro hx; exact ⟨x, hx, 0, le_rfl, by simp⟩
        rw [this]; exact hK'
      · have huu : inner ℝ u u ≠ 0 := by
          rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
        let P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.id ℝ _ - (inner ℝ u u)⁻¹ • ((innerSL ℝ u).smulRight u)
        have hP : ∀ x, P x = x - ((inner ℝ u u)⁻¹ * inner ℝ u x) • u := by
          intro x; simp [P, mul_smul]
        have hPu : P u = 0 := by rw [hP, inv_mul_cancel₀ huu, one_smul, sub_self]
        have hker : ∀ z, P z = 0 → z = ((inner ℝ u u)⁻¹ * inner ℝ u z) • u := by
          intro z hz; rw [hP] at hz; exact sub_eq_zero.1 hz
        have hclosed := ih (fun i => P (v i))
        have : conicSet (insert a s) v = P ⁻¹' (conicSet s (fun i => P (v i))) := by
          rw [hK]; ext x
          constructor
          · rintro ⟨y, ⟨μ, hμ, rfl⟩, t, _, rfl⟩
            refine ⟨μ, hμ, ?_⟩
            simp [map_sum, map_smul, hPu, ← hu]
          · intro hx
            obtain ⟨μ, hμ, hPx⟩ := hx
            have hy : (∑ i ∈ s, μ i • v i) ∈ K' := ⟨μ, hμ, rfl⟩
            have hz : P (x - ∑ i ∈ s, μ i • v i) = 0 := by
              rw [map_sub, map_sum]
              simp only [map_smul]
              exact sub_eq_zero.2 hPx
            have hx' := hker _ hz
            set c := (inner ℝ u u)⁻¹ * inner ℝ u (x - ∑ i ∈ s, μ i • v i) with hc
            by_cases hc0 : 0 ≤ c
            · exact ⟨_, hy, c, hc0, by rw [← hx']; abel⟩
            · have h1 : (-c) • (-u) ∈ K' := conicSet_smul hneg (by linarith)
              have h2 : (∑ i ∈ s, μ i • v i) + (-c) • (-u) ∈ K' := conicSet_add hy h1
              refine ⟨_, h2, 0, le_rfl, ?_⟩
              rw [zero_smul, add_zero, neg_smul_neg, ← hx']
              abel
        rw [this]; exact hclosed.preimage P.continuous
    · -- Case 1: -u is not in the cone
      have hne : (K' : Set _).Nonempty := ⟨0, conicSet_zero _ _⟩
      have hδ : 0 < Metric.infDist (-u) K' := (hK'.notMem_iff_infDist_pos hne).1 hneg
      set δ := Metric.infDist (-u) K' with hδdef
      have hlow : ∀ y ∈ K', ∀ t : ℝ, 0 ≤ t → δ * t ≤ ‖y + t • u‖ := by
        intro y hy t ht
        rcases ht.eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · have hyt : t⁻¹ • y ∈ K' := conicSet_smul hy (inv_nonneg.2 ht)
          have h1 : δ ≤ dist (-u) (t⁻¹ • y) := Metric.infDist_le_dist_of_mem hyt
          have h2 : dist (-u) (t⁻¹ • y) = t⁻¹ * ‖y + t • u‖ := by
            rw [dist_eq_norm]
            have : -u - t⁻¹ • y = -(t⁻¹ • (y + t • u)) := by
              rw [smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]; abel
            rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht)]
          rw [h2] at h1
          have := mul_le_mul_of_nonneg_left h1 ht
          rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
      rw [hK]
      apply isClosed_of_closure_subset
      intro x hx
      obtain ⟨z, hzK, hz⟩ := mem_closure_iff_seq_limit.1 hx
      choose y hy t ht hzyt using hzK
      obtain ⟨R, hR⟩ := (hz.norm).bddAbove_range
      have htb : ∀ k, t k ∈ Set.Icc (0 : ℝ) (R / δ) := by
        intro k
        refine ⟨ht k, ?_⟩
        have h1 := hlow (y k) (hy k) (t k) (ht k)
        have h2 : ‖z k‖ ≤ R := hR ⟨k, rfl⟩
        rw [hzyt k] at h2
        rw [le_div_iff₀ hδ]; nlinarith
      obtain ⟨t0, ht0, φ, hφ, hlim⟩ := (isCompact_Icc).tendsto_subseq htb
      have hyl : Tendsto (fun k => y (φ k)) atTop (𝓝 (x - t0 • u)) := by
        have h1 : Tendsto (fun k => z (φ k) - t (φ k) • u) atTop (𝓝 (x - t0 • u)) :=
          (hz.comp hφ.tendsto_atTop).sub (hlim.smul_const u)
        refine h1.congr (fun k => ?_)
        rw [hzyt (φ k)]; simp
      have hmem : x - t0 • u ∈ K' := hK'.mem_of_tendsto hyl (Filter.Eventually.of_forall (fun k => hy _))
      exact ⟨_, hmem, t0, ht0.1, by abel⟩

lemma farkas [Fintype ι] (v : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (h : ∀ d, (∀ i, inner ℝ (v i) d ≤ 0) → inner ℝ w d ≤ 0) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ w = ∑ i, μ i • v i := by
  by_contra hcon
  have hw : w ∉ conicSet Finset.univ v := fun ⟨μ, hμ, e⟩ =>
    hcon ⟨μ, fun i => hμ i (Finset.mem_univ i), e⟩
  have hcl := conicSet_isClosed (n := n) Finset.univ v
  have hcv := conicSet_convex (n := n) Finset.univ v
  obtain ⟨p, hp, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex ⟨0, conicSet_zero _ _⟩
    hcl.isComplete hcv w
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).1 hpmin
  have h0 := hvar 0 (conicSet_zero _ _)
  have h2 := hvar (2 • p) (by simpa [two_smul] using conicSet_add hp hp)
  have hdp : inner ℝ (w - p) p = 0 := by
    have e1 : inner ℝ (w - p) (0 - p) = - inner ℝ (w - p) p := by simp
    have e2 : inner ℝ (w - p) (2 • p - p) = inner ℝ (w - p) p := by
      rw [two_smul, add_sub_cancel_right]
    linarith
  have hk : ∀ k ∈ conicSet Finset.univ v, inner ℝ (w - p) k ≤ 0 := by
    intro k hk
    have := hvar k hk
    rw [inner_sub_right, hdp] at this
    linarith
  have hvi : ∀ i, inner ℝ (v i) (w - p) ≤ 0 := by
    intro i
    rw [real_inner_comm]
    apply hk
    refine ⟨Pi.single i 1, fun j _ => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · simp [Pi.single_apply, Finset.sum_ite_eq']
  have hwd := h _ hvi
  have hne : w - p ≠ 0 := fun e => hw (by rw [sub_eq_zero.1 e]; exact hp)
  have : inner ℝ w (w - p) = ‖w - p‖ ^ 2 + inner ℝ p (w - p) := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_left]; congr 1; abel
  have hpd : inner ℝ p (w - p) = 0 := by rw [real_inner_comm]; exact hdp
  have hpos : 0 < ‖w - p‖ ^ 2 := by positivity
  linarith
end FarkasLib

lemma farkas_repr {n m p : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : Fin p → EuclideanSpace ℝ (Fin n)) (act : Fin p → Prop) [DecidablePred act]
    (w : EuclideanSpace ℝ (Fin n))
    (hw : ∀ d, (∀ i, inner ℝ (a i) d = 0) → (∀ j, act j → inner ℝ (b j) d ≤ 0) →
      inner ℝ w d ≤ 0) :
    ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, ¬ act j → mu j = 0) ∧
      w = ∑ i, lam i • a i + ∑ j, mu j • b j := by
  let v : Fin m ⊕ Fin m ⊕ Fin p → EuclideanSpace ℝ (Fin n) := fun k =>
    match k with
    | Sum.inl i => a i
    | Sum.inr (Sum.inl i) => -a i
    | Sum.inr (Sum.inr j) => if act j then b j else 0
  have hfar : ∀ d, (∀ k, inner ℝ (v k) d ≤ 0) → inner ℝ w d ≤ 0 := by
    intro d hd
    apply hw d
    · intro i
      have h1 := hd (Sum.inl i)
      have h2 := hd (Sum.inr (Sum.inl i))
      simp only [v, inner_neg_left] at h1 h2
      linarith
    · intro j hj
      have := hd (Sum.inr (Sum.inr j))
      simpa [v, hj] using this
  obtain ⟨μ, hμ, hwe⟩ := farkas v w hfar
  refine ⟨fun i => μ (Sum.inl i) - μ (Sum.inr (Sum.inl i)),
    fun j => if act j then μ (Sum.inr (Sum.inr j)) else 0, ?_, ?_, ?_⟩
  · intro j; dsimp only; split_ifs
    · exact hμ _
    · exact le_rfl
  · intro j hj; simp [hj]
  · rw [hwe, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [v, smul_neg, Finset.sum_neg_distrib, sub_smul, Finset.sum_sub_distrib]
    have : ∑ j, μ (Sum.inr (Sum.inr j)) • (if act j then b j else 0) =
        ∑ j, (if act j then μ (Sum.inr (Sum.inr j)) else 0) • b j := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [this]
    abel

lemma linSet_zero_cone {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p) (x z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ C.linSet x 0) {c : ℝ} (hc : 0 ≤ c) : x + c • (z - x) ∈ C.linSet x 0 := by
  refine ⟨fun i => ?_, fun j hj => ?_, fun j h1 h2 => ?_⟩
  · simp [inner_smul_right, hz.1 i]
  · simp only [add_sub_cancel_left, inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hc (hz.2.1 j hj)
  · exfalso
    have : (0 : ℝ) < C.g j x := by exact_mod_cast h1
    linarith


lemma self_mem_linSet' {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) (γ : EReal) :
    x ∈ C.linSet x γ :=
  ⟨fun i => by simp, fun j _ => by simp, fun j _ h2 => by simpa using h2.le⟩

lemma linSet_convex {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) (γ : EReal) :
    Convex ℝ (C.linSet x γ) := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  have hb' : b = 1 - a := by linarith
  have e : a • z1 + b • z2 - x = a • (z1 - x) + b • (z2 - x) := by
    subst hb'; module
  refine ⟨fun i => ?_, fun j hj => ?_, fun j h1 h2 => ?_⟩
  · rw [e, inner_add_right, inner_smul_right, inner_smul_right, hz1.1 i, hz2.1 i]; simp
  · rw [e, inner_add_right, inner_smul_right, inner_smul_right]
    have := hz1.2.1 j hj
    have := hz2.2.1 j hj
    nlinarith [mul_nonneg ha (neg_nonneg.2 (hz1.2.1 j hj)), mul_nonneg hb (neg_nonneg.2 (hz2.2.1 j hj))]
  · rw [e, inner_add_right, inner_smul_right, inner_smul_right]
    have h3 := hz1.2.2 j h1 h2
    have h4 := hz2.2.2 j h1 h2
    have hg : C.g j x = a * C.g j x + b * C.g j x := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha (neg_nonneg.2 h3), mul_nonneg hb (neg_nonneg.2 h4)]

lemma linSet_isClosed {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) (γ : EReal) :
    IsClosed (C.linSet x γ) := by
  have c1 : ∀ i, Continuous fun z : EuclideanSpace ℝ (Fin n) =>
      inner ℝ (gradient (C.h i) x) (z - x) := fun i => by fun_prop
  have c2 : ∀ j, Continuous fun z : EuclideanSpace ℝ (Fin n) =>
      inner ℝ (gradient (C.g j) x) (z - x) := fun j => by fun_prop
  have c3 : ∀ j, Continuous fun z : EuclideanSpace ℝ (Fin n) =>
      C.g j x + inner ℝ (gradient (C.g j) x) (z - x) := fun j => by fun_prop
  have e : C.linSet x γ = (⋂ i, {z | inner ℝ (gradient (C.h i) x) (z - x) = 0}) ∩
      ((⋂ j, {z | 0 ≤ C.g j x → inner ℝ (gradient (C.g j) x) (z - x) ≤ 0}) ∩
       (⋂ j, {z | γ < (C.g j x : EReal) → C.g j x < 0 →
          C.g j x + inner ℝ (gradient (C.g j) x) (z - x) ≤ 0})) := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]; exact Iff.rfl
  rw [e]
  refine (isClosed_iInter fun i => isClosed_eq (c1 i) continuous_const).inter
    ((isClosed_iInter fun j => ?_).inter (isClosed_iInter fun j => ?_))
  · by_cases h : 0 ≤ C.g j x
    · simp only [h, true_implies]
      exact isClosed_le (c2 j) continuous_const
    · simp [h]
  · by_cases h : γ < (C.g j x : EReal) ∧ C.g j x < 0
    · have : {z : EuclideanSpace ℝ (Fin n) | γ < (C.g j x : EReal) → C.g j x < 0 →
          C.g j x + inner ℝ (gradient (C.g j) x) (z - x) ≤ 0} =
          {z | C.g j x + inner ℝ (gradient (C.g j) x) (z - x) ≤ 0} := by
        ext z; simp [h.1, h.2]
      rw [this]
      exact isClosed_le (c3 j) continuous_const
    · have : {z : EuclideanSpace ℝ (Fin n) | γ < (C.g j x : EReal) → C.g j x < 0 →
          C.g j x + inner ℝ (gradient (C.g j) x) (z - x) ≤ 0} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ h
      rw [this]; exact isClosed_univ

lemma exists_proj {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ∃ y, IsProj S z y := by
  obtain ⟨v, hv, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv z
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : EuclideanSpace ℝ (Fin n))‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨v, hv, fun w hw => by rw [hvmin]; exact ciInf_le hb ⟨w, hw⟩⟩

lemma gradient_continuous {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  have h : gradient f = fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ f x) := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hf.continuous_fderiv one_ne_zero)

lemma gradient_linear {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun x : EuclideanSpace ℝ (Fin n) => -inner ℝ w x) x = -w := by
  apply HasGradientAt.gradient
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => -inner ℝ w x) (-(innerSL ℝ w)) x :=
    ((innerSL ℝ w).hasFDerivAt (x := x)).neg
  have h2 : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (-w) = -(innerSL ℝ w) := by
    ext v; simp [InnerProductSpace.toDual_apply_apply]
  rw [hasGradientAt_iff_hasFDerivAt, h2]
  exact h1

lemma normal_shift {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p) (x ε : EuclideanSpace ℝ (Fin n))
    (hxε : x + ε ∈ C.linSet x 0) :
    normalCone (C.linSet x 0) (x + ε) ⊆ normalCone (C.linSet x 0) x := by
  have hx : x ∈ C.linSet x 0 := self_mem_linSet' C x 0
  intro w hw
  have h0 := hw.2 x hx
  have h2 := hw.2 (x + (2:ℝ) • ((x + ε) - x)) (linSet_zero_cone C x _ hxε (by norm_num))
  have e0 : x - (x + ε) = -ε := by abel
  have e2 : x + (2:ℝ) • ((x + ε) - x) - (x + ε) = ε := by
    rw [add_sub_cancel_left, two_smul]; abel
  rw [e0, inner_neg_right] at h0
  rw [e2] at h2
  have hε : inner ℝ w ε = 0 := le_antisymm h2 (by linarith)
  refine ⟨hx, fun z hz => ?_⟩
  have := hw.2 z hz
  have e3 : z - x = (z - (x + ε)) + ε := by abel
  rw [e3, inner_add_right, hε]; linarith

lemma normal_to_proj {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hcv : Convex ℝ S)
    {x w : EuclideanSpace ℝ (Fin n)} (h : w ∈ normalCone S x) : IsProj S (x + w) x := by
  refine ⟨h.1, min_of_inner_le hcv h.1 ?_⟩
  intro z hz
  rw [add_sub_cancel_left]; exact h.2 z hz

lemma proj_to_normal {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hcv : Convex ℝ S)
    {x w : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (h : IsProj S (x + w) x) :
    w ∈ normalCone S x := by
  refine ⟨hx, fun z hz => ?_⟩
  have := inner_le_of_min hcv hx h.2 z hz
  rwa [add_sub_cancel_left] at this


theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (γ : EReal) (hγ : γ < 0)
    (x ε : ℕ → EuclideanSpace ℝ (Fin n)) (hx : Tendsto x atTop (𝓝 xs))
    (hε : Tendsto ε atTop (𝓝 0)) (hy : ∀ k, x k + ε k ∈ C.linSet (x k) γ) :
    ∀ᶠ k in atTop,
      normalCone (C.linSet (x k) γ) (x k + ε k) ⊆
        normalCone (C.linSet (x k) ⊥) (x k + ε k) := by
  have key : ∀ᶠ k in atTop, x k + ε k ∈ C.linSet (x k) ⊥ := by
    induction γ using EReal.rec with
    | bot => exact Filter.Eventually.of_forall hy
    | top => exact absurd hγ (by simp)
    | coe c =>
      have hc : c < 0 := by exact_mod_cast hγ
      have hev : ∀ j, ∀ᶠ k in atTop, inner ℝ (gradient (C.g j) (x k)) (ε k) ≤ -c := by
        intro j
        have hg := gradient_continuous (hC.2 j)
        have h1 : Tendsto (fun k => inner ℝ (gradient (C.g j) (x k)) (ε k)) atTop
            (𝓝 (inner ℝ (gradient (C.g j) xs) (0 : EuclideanSpace ℝ (Fin n)))) :=
          Filter.Tendsto.inner ((hg.tendsto xs).comp hx) hε
        rw [inner_zero_right] at h1
        exact h1.eventually (ge_mem_nhds (by linarith))
      filter_upwards [Filter.eventually_all.2 hev] with k hk
      refine ⟨(hy k).1, (hy k).2.1, fun j h1 h2 => ?_⟩
      rw [add_sub_cancel_left]
      by_cases hcg : c < C.g j (x k)
      · have := (hy k).2.2 j (by exact_mod_cast hcg) h2
        rwa [add_sub_cancel_left] at this
      · have := hk j
        have hcg' := not_lt.1 hcg
        linarith
  filter_upwards [key] with k hk
  intro w hw
  refine ⟨hk, fun z hz => hw.2 z ?_⟩
  exact ⟨hz.1, hz.2.1, fun j h1 h2 => hz.2.2 j (EReal.bot_lt_coe _) h2⟩
