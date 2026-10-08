-- Prove2me | solution 1 for PolicyGradTheory.ChainLB.resolvent_derivative_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:34:48.415969+00:00
-- url     : https://prove2.me/submissions/41e751a1-c0c0-4546-bf43-492658b85e6c

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain

open scoped Matrix.Norms.Operator

namespace PolicyGradTheory.ChainLB

open FoundationsML.ReinforcementLearning

lemma induced_eq_core (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s s' : Fin (H + 2)) :
    InducedTransition (chainPolicy H θ) (chainP H) s s' = chainMatrix H (forwardProb H θ) s s' := by
  unfold InducedTransition chainPolicy chainP chainMatrix forwardProb
  rw [Fin.sum_univ_four]
  by_cases h0 : s.val = 0
  · simp [h0]
  by_cases h1 : s.val = H + 1
  · have : ¬ (0 < s.val ∧ s.val ≤ H) := by omega
    simp [h1, this]
  have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
  simp [h0, h1, hs]
  split_ifs <;> first | (exfalso; omega) | ring

lemma chainMatrix_nonneg (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s s' : Fin (H + 2)) : 0 ≤ chainMatrix H p s s' := by
  unfold chainMatrix
  split_ifs <;> first | exact (hp _).1 | exact sub_nonneg.2 (hp _).2 | norm_num

lemma chainMatrix_rowsum (H : ℕ) (p : Fin H → ℝ) (s : Fin (H + 2)) :
    ∑ s', chainMatrix H p s s' = 1 := by
  by_cases h0 : s.val = 0
  · have : ∀ s' : Fin (H + 2), chainMatrix H p s s' = if s' = ⟨1, by omega⟩ then 1 else 0 := by
      intro s'; unfold chainMatrix; simp [h0, Fin.ext_iff]
    rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq']; simp
  by_cases h1 : s.val = H + 1
  · have : ∀ s' : Fin (H + 2), chainMatrix H p s s' = if s' = s then 1 else 0 := by
      intro s'; unfold chainMatrix; simp [h0, h1]
    simp [this]
  have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
  have : ∀ s' : Fin (H + 2), chainMatrix H p s s' =
      p ⟨s.val - 1, by omega⟩ * (if s' = ⟨s.val + 1, by omega⟩ then 1 else 0) +
      (1 - p ⟨s.val - 1, by omega⟩) * (if s' = ⟨s.val - 1, by omega⟩ then 1 else 0) := by
    intro s'; unfold chainMatrix
    simp only [h0, h1, hs, and_self, dif_pos, if_false, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

lemma pow_bounds (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℕ) :
    (∀ s s', 0 ≤ (chainMatrix H p ^ t) s s') ∧ ∀ s, ∑ s', (chainMatrix H p ^ t) s s' = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s s' => ?_, fun s => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun s s' => ?_, fun s => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.1 _ _) (chainMatrix_nonneg H p hp _ _)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp [← Finset.mul_sum, chainMatrix_rowsum, ih.2]

lemma pow_le_one (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℕ)
    (s s' : Fin (H + 2)) : (chainMatrix H p ^ t) s s' ≤ 1 := by
  have h := pow_bounds H p hp t
  rw [← h.2 s]
  exact Finset.single_le_sum (fun k _ => h.1 s k) (Finset.mem_univ s')

lemma gamma_bounds (H : ℕ) : 0 ≤ chainGamma H ∧ chainGamma H < 1 := by
  unfold chainGamma
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

lemma summable_entry (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s s' : Fin (H + 2)) :
    Summable (fun t : ℕ => chainGamma H ^ t * (chainMatrix H p ^ t) s s') := by
  obtain ⟨g0, g1⟩ := gamma_bounds H
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg g0 _)
    ((pow_bounds H p hp t).1 s s')) (fun t => ?_) (summable_geometric_of_lt_one g0 g1)
  calc chainGamma H ^ t * (chainMatrix H p ^ t) s s' ≤ chainGamma H ^ t * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one H p hp t s s') (pow_nonneg g0 _)
    _ = _ := mul_one _

lemma neumann_right_inv (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (1 - chainGamma H • chainMatrix H p) *
      Matrix.of (fun s s' => ∑' t : ℕ, chainGamma H ^ t * (chainMatrix H p ^ t) s s') = 1 := by
  ext i j
  set A := chainMatrix H p
  set γ := chainGamma H
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul]
  simp only [Matrix.of_apply]
  have hs := summable_entry H p hp
  have h1 : ∑ k, A i k * ∑' t : ℕ, γ ^ t * (A ^ t) k j = ∑' t : ℕ, γ ^ t * (A ^ (t + 1)) i j := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun k _ => (hs k j).mul_left _)]
    congr 1; ext t
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    congr 1; ext k; ring
  rw [h1, (hs i j).tsum_eq_zero_add]
  rw [← tsum_mul_left]
  simp only [pow_zero, one_mul]
  have : ∀ t : ℕ, γ * (γ ^ t * (A ^ (t + 1)) i j) = γ ^ (t + 1) * (A ^ (t + 1)) i j := by
    intro t; ring
  simp_rw [this]
  ring

lemma resolvent_eq_tsum (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    chainResolvent H p = Matrix.of (fun s s' => ∑' t : ℕ, chainGamma H ^ t * (chainMatrix H p ^ t) s s') :=
  Matrix.inv_eq_right_inv (neumann_right_inv H p hp)

theorem chain_value_eq_resolvent_core (H : ℕ)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1) :
    chainValue H θ = chainResolvent H (forwardProb H θ) 0 (Fin.last (H + 1)) := by
  have hp : ∀ i, 0 ≤ forwardProb H θ i ∧ forwardProb H θ i ≤ 1 :=
    fun i => ⟨(hθ i 0).1.le, (hθ i 0).2.le⟩
  rw [resolvent_eq_tsum H _ hp, Matrix.of_apply]
  unfold chainValue PolicyValue
  have hocc : ∀ t s', OccupationDist (chainPolicy H θ) (chainP H) 0 t s' =
      (chainMatrix H (forwardProb H θ) ^ t) 0 s' := by
    intro t
    induction t with
    | zero => intro s'; simp [OccupationDist, Matrix.one_apply, eq_comm]
    | succ t ih =>
      intro s'
      simp only [OccupationDist, ih, induced_eq_core, pow_succ, Matrix.mul_apply]
  have hrew : ∀ s', InducedReward (chainPolicy H θ) (chainR H) s' =
      if s' = Fin.last (H + 1) then 1 else 0 := by
    intro s'
    unfold InducedReward chainR chainPolicy
    rw [Fin.sum_univ_four]
    by_cases h : s' = Fin.last (H + 1)
    · have : ¬ (0 < s'.val ∧ s'.val ≤ H) := by subst h; simp
      simp [h, this]
    · simp [h]
  congr 1; ext t
  simp [hocc, hrew]


/-- the linear part of `chainMatrix`. -/
noncomputable def chainLin (H : ℕ) :
    (Fin H → ℝ) →ₗ[ℝ] Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ where
  toFun q := chainMatrix H q - chainMatrix H 0
  map_add' x y := by
    ext s s'
    simp only [Matrix.sub_apply, Matrix.add_apply, chainMatrix]
    split_ifs <;> simp <;> ring
  map_smul' c x := by
    ext s s'
    simp only [Matrix.sub_apply, Matrix.smul_apply, chainMatrix, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp <;> ring

lemma chainLin_single (H : ℕ) (i : Fin H) (s s' : Fin (H + 2)) :
    chainLin H (Pi.single i 1) s s' =
      if s = ⟨i.val + 1, by omega⟩ then
        ((if s' = ⟨i.val + 2, by omega⟩ then 1 else 0) - (if s' = ⟨i.val, by omega⟩ then 1 else 0))
      else 0 := by
  show (chainMatrix H (Pi.single i 1) - chainMatrix H 0) s s' = _
  simp only [Matrix.sub_apply, chainMatrix, Fin.ext_iff, Pi.single_apply, Pi.zero_apply]
  split_ifs <;> first | (exfalso; omega) | ring

theorem resolvent_derivative_identity_core (H : ℕ)
    (p : Fin H → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (a b : Fin (H + 2)) (i : Fin H) :
    fderiv ℝ (fun q : Fin H → ℝ => chainResolvent H q a b) p (Pi.single i (1 : ℝ)) =
      chainGamma H * chainResolvent H p a ⟨i.val + 1, by omega⟩ *
        (chainResolvent H p ⟨i.val + 2, by omega⟩ b -
         chainResolvent H p ⟨i.val, by omega⟩ b) := by
  have hp' : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨(hp i).1.le, (hp i).2.le⟩
  let Lc : (Fin H → ℝ) →L[ℝ] (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) := LinearMap.toContinuousLinearMap (chainLin H)
  let F : (Fin H → ℝ) → (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) := fun q => 1 - chainGamma H • chainMatrix H q
  have hF : HasFDerivAt F (-(chainGamma H • Lc)) p := by
    have h1 : HasFDerivAt (fun q => chainMatrix H 0 + Lc q) Lc p :=
      Lc.hasFDerivAt.const_add _
    have h2 : (fun q => chainMatrix H 0 + Lc q) = fun q => chainMatrix H q := by
      funext q; show chainMatrix H 0 + (chainMatrix H q - chainMatrix H 0) = _; abel
    rw [h2] at h1
    have h3 := (h1.const_smul (chainGamma H)).const_sub (1 : (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ))
    exact h3
  have hU : IsUnit (F p) := by
    have := Matrix.isUnit_det_of_right_inverse (neumann_right_inv H p hp')
    exact (Matrix.isUnit_iff_isUnit_det _).2 this
  obtain ⟨u, hu⟩ := hU
  have hG : HasFDerivAt (fun q => Ring.inverse (F q))
      ((-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) ↑u⁻¹ ↑u⁻¹).comp (-(chainGamma H • Lc))) p := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at this
    exact this.comp p hF
  have hbd : ∀ A : (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ), ‖Matrix.entryLinearMap ℝ ℝ a b A‖ ≤ 1 * ‖A‖ := by
    intro A
    rw [one_mul, Matrix.entryLinearMap_apply]
    have : ‖A a b‖₊ ≤ ‖A‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      exact (Finset.single_le_sum (f := fun j => ‖A a j‖₊) (fun _ _ => by positivity)
        (Finset.mem_univ b)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a))
    exact_mod_cast this
  let e := (Matrix.entryLinearMap ℝ ℝ a b).mkContinuous 1 hbd
  have hE := e.hasFDerivAt.comp p hG
  have hfun : (fun q : Fin H → ℝ => chainResolvent H q a b) = e ∘ fun q => Ring.inverse (F q) := by
    funext q
    simp [e, chainResolvent, F, Matrix.nonsing_inv_eq_ringInverse, LinearMap.mkContinuous_apply, Matrix.entryLinearMap_apply]
  rw [hfun, hE.fderiv]
  have hM : (↑u⁻¹ : (Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ)) = chainResolvent H p := by
    rw [chainResolvent, Matrix.nonsing_inv_eq_ringInverse]
    show _ = Ring.inverse (F p)
    rw [← hu, Ring.inverse_unit]
  change ((-((↑u⁻¹ : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) *
    (-(chainGamma H • chainLin H (Pi.single i 1))) * (↑u⁻¹ : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ))) :
      Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) a b = _
  rw [hM]
  set M := chainResolvent H p
  simp only [mul_neg, neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, chainLin_single]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    ite_mul, zero_mul]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq]
  ring

end PolicyGradTheory.ChainLB

open PolicyGradTheory.ChainLB


theorem solution (H : ℕ) (hH : 1 ≤ H)
    (p : Fin H → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (a b : Fin (H + 2)) (i : Fin H) :
    fderiv ℝ (fun q : Fin H → ℝ => chainResolvent H q a b) p (Pi.single i (1 : ℝ)) =
      chainGamma H * chainResolvent H p a ⟨i.val + 1, by omega⟩ *
        (chainResolvent H p ⟨i.val + 2, by omega⟩ b -
         chainResolvent H p ⟨i.val, by omega⟩ b) := by
  exact resolvent_derivative_identity_core H p hp a b i
