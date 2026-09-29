-- Prove2me | solution 1 for SupportVectorMachines.Kernels.corollary_4_17_limits_of_kernels
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T02:41:30.772925+00:00
-- url     : https://prove2.me/submissions/63693741-0269-4d75-bfa5-105c88c5831f

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel

set_option autoImplicit false

theorem svm_gram_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → E) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, c a * c b * inner ℝ (v b) (v a) := by
  have h : ∑ a ∈ s, ∑ b ∈ s, c a * c b * inner ℝ (v b) (v a) =
      inner ℝ (∑ b ∈ s, c b • v b) (∑ a ∈ s, c a • v a) := by
    rw [sum_inner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [h]
  exact real_inner_self_nonneg

open SupportVectorMachines.Kernels in
theorem solution {X : Type*} (kn : ℕ → X → X → ℝ) (k : X → X → ℝ)
    (hkn : ∀ n, IsKernel (kn n))
    (hlim : ∀ x x' : X, Filter.Tendsto (fun n => kn n x x') Filter.atTop (nhds (k x x'))) :
    IsKernel k := by
  choose H i1 i2 i3 Φ hΦ using hkn
  let Ψ : X → ((n : ℕ) → H n) := fun x n => Φ n x
  have hfac : ∀ x₁ x₂ y₁ y₂ : X, Ψ x₁ = Ψ y₁ → Ψ x₂ = Ψ y₂ → k x₁ x₂ = k y₁ y₂ := by
    intro x₁ x₂ y₁ y₂ h1 h2
    have hseq : (fun n => kn n x₁ x₂) = fun n => kn n y₁ y₂ := by
      funext n
      rw [hΦ, hΦ]
      have e1 : Φ n x₁ = Φ n y₁ := congrFun h1 n
      have e2 : Φ n x₂ = Φ n y₂ := congrFun h2 n
      rw [e1, e2]
    have h := hlim x₁ x₂
    rw [hseq] at h
    exact tendsto_nhds_unique h (hlim y₁ y₂)
  have hsymm : ∀ x y, k x y = k y x := by
    intro x y
    have hseq : (fun n => kn n x y) = fun n => kn n y x := by
      funext n
      rw [hΦ, hΦ]
      let _ : NormedAddCommGroup (H n) := i1 n
      let _ : InnerProductSpace ℝ (H n) := i2 n
      exact real_inner_comm _ _
    have h := hlim x y
    rw [hseq] at h
    exact tendsto_nhds_unique h (hlim y x)
  have hpd : ∀ {ι : Type} (s : Finset ι) (c : ι → ℝ) (p : ι → X),
      0 ≤ ∑ a ∈ s, ∑ b ∈ s, c a * c b * k (p b) (p a) := by
    intro ι s c p
    have ht : Filter.Tendsto (fun n => ∑ a ∈ s, ∑ b ∈ s, c a * c b * kn n (p b) (p a))
        Filter.atTop (nhds (∑ a ∈ s, ∑ b ∈ s, c a * c b * k (p b) (p a))) := by
      refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
      exact (hlim (p b) (p a)).const_mul (c a * c b)
    refine ge_of_tendsto' ht fun n => ?_
    simp only [hΦ n]
    let _ : NormedAddCommGroup (H n) := i1 n
    let _ : InnerProductSpace ℝ (H n) := i2 n
    exact svm_gram_nonneg s c (fun a => Φ n (p a))
  let Y : Type := Set.range Ψ
  let pick : Y → X := fun y => Classical.choose y.2
  have hpick : ∀ y : Y, Ψ (pick y) = y.1 := fun y => Classical.choose_spec y.2
  let kY : Y → Y → ℝ := fun a b => k (pick a) (pick b)
  let K : Matrix Y Y (ℝ →L[ℝ] ℝ) := Matrix.of fun a b => kY a b • (1 : ℝ →L[ℝ] ℝ)
  have hK : K.PosSemidef := by
    have htf := (RKHS.posSemidef_tfae (𝕜 := ℝ) (K := K)).out 0 2
    refine htf.mpr ⟨?_, ?_⟩
    · refine Matrix.ext fun a b => ?_
      rw [Matrix.conjTranspose_apply]
      simp only [K, kY, Matrix.of_apply, star_smul, star_one, star_trivial]
      rw [hsymm]
    · intro vv
      simp [Finsupp.sum, K, kY]
      refine le_of_le_of_eq (hpd vv.support vv pick)
        (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  have : Fact K.PosSemidef := ⟨hK⟩
  refine ⟨RKHS.OfKernel K, inferInstance, inferInstance, inferInstance,
    fun x => RKHS.kerFun (RKHS.OfKernel K) ⟨Ψ x, x, rfl⟩ 1, ?_⟩
  intro x x'
  rw [RKHS.kerFun_inner, RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel]
  simp [K, kY]
  exact hfac _ _ _ _ (hpick ⟨Ψ x, x, rfl⟩).symm (hpick ⟨Ψ x', x', rfl⟩).symm
