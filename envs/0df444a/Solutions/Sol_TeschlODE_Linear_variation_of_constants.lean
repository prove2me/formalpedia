-- Prove2me | solution 1 for TeschlODE.Linear.variation_of_constants
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:19:07.520168+00:00
-- url     : https://prove2.me/submissions/9ca867aa-acf6-4b2b-b41f-5ac90649705e

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

open Set Filter Topology
open scoped Matrix NNReal

namespace VocAux

/-- Multiplication by a real matrix as a continuous linear map on `ℝⁿ`. -/
noncomputable def mvCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin n → ℝ) (F' := Fin n → ℝ)).toLinearMap ∘ₗ
    (Matrix.toLin' : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).toLinearMap

lemma mvCLM_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    mvCLM B x = B *ᵥ x := by
  simp [mvCLM]

lemma continuous_mvCLM {n : ℕ} : Continuous (mvCLM (n := n)) :=
  LinearMap.continuous_of_finiteDimensional _

/-- Around a point `t` of a set `I` containing no points beyond... (order-connectedness is used
only by the callers) there is a compact interval with endpoints in `I` which is a neighbourhood
of `t` relative to `I`. -/
lemma exists_Icc_mem_nhdsWithin {I : Set ℝ} {t : ℝ} (ht : t ∈ I) :
    ∃ a b, a ∈ I ∧ b ∈ I ∧ a ≤ t ∧ t ≤ b ∧ Icc a b ∈ 𝓝[I] t := by
  by_cases hb : ∃ b ∈ I, t < b <;> by_cases ha : ∃ a ∈ I, a < t
  · obtain ⟨b, hbI, htb⟩ := hb
    obtain ⟨a, haI, hat⟩ := ha
    refine ⟨a, b, haI, hbI, hat.le, htb.le, ?_⟩
    refine mem_nhdsWithin.2 ⟨Ioo a b, isOpen_Ioo, ⟨hat, htb⟩, ?_⟩
    exact fun s hs => Ioo_subset_Icc_self hs.1
  · obtain ⟨b, hbI, htb⟩ := hb
    push Not at ha
    refine ⟨t, b, ht, hbI, le_rfl, htb.le, ?_⟩
    refine mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, htb, ?_⟩
    exact fun s hs => ⟨ha s hs.2, hs.1.le⟩
  · obtain ⟨a, haI, hat⟩ := ha
    push Not at hb
    refine ⟨a, t, haI, ht, hat.le, le_rfl, ?_⟩
    refine mem_nhdsWithin.2 ⟨Ioi a, isOpen_Ioi, hat, ?_⟩
    exact fun s hs => ⟨hs.1.le, hb s hs.2⟩
  · push Not at ha hb
    refine ⟨t, t, ht, ht, le_rfl, le_rfl, ?_⟩
    refine mem_nhdsWithin.2 ⟨univ, isOpen_univ, mem_univ _, ?_⟩
    exact fun s hs => ⟨ha s hs.2, hb s hs.2⟩

/-- Fundamental theorem of calculus for a function continuous on an order-connected set,
with the derivative taken within that set. -/
lemma hasDerivWithinAt_integral {n : ℕ} {I : Set ℝ} (hI : I.OrdConnected)
    {h : ℝ → Fin n → ℝ} (hh : ContinuousOn h I) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivWithinAt (fun τ => ∫ s in t₀..τ, h s) (h t) I t := by
  obtain ⟨a, b, haI, hbI, hat, htb, hnhds⟩ := exists_Icc_mem_nhdsWithin ht
  set a' := min a t₀ with ha'
  set b' := max b t₀ with hb'
  have ha'I : a' ∈ I := by rcases min_choice a t₀ with h | h <;> rw [ha', h] <;> assumption
  have hb'I : b' ∈ I := by rcases max_choice b t₀ with h | h <;> rw [hb', h] <;> assumption
  have hsub : Icc a' b' ⊆ I := hI.out ha'I hb'I
  have hnhds' : Icc a' b' ∈ 𝓝[I] t :=
    Filter.mem_of_superset hnhds (Icc_subset_Icc (min_le_left _ _) (le_max_left _ _))
  have hat' : a' ≤ t := (min_le_left _ _).trans hat
  have htb' : t ≤ b' := htb.trans (le_max_left _ _)
  have ht₀' : t₀ ∈ Icc a' b' := ⟨min_le_right _ _, le_max_right _ _⟩
  have ht' : t ∈ Icc a' b' := ⟨hat', htb'⟩
  -- a globally continuous modification
  set hbar : ℝ → Fin n → ℝ := fun s => h (max a' (min b' s)) with hhbar
  have hmem : ∀ s, max a' (min b' s) ∈ Icc a' b' := by
    intro s
    have hab : a' ≤ b' := hat'.trans htb'
    refine ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcont : Continuous hbar :=
    (hh.mono hsub).comp_continuous (by fun_prop) hmem
  have hbar_eq : ∀ s ∈ Icc a' b', hbar s = h s := by
    intro s hs
    simp only [hhbar]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  have hD : HasDerivAt (fun τ => ∫ s in t₀..τ, hbar s) (hbar t) t :=
    (hcont.integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hD' : HasDerivWithinAt (fun τ => ∫ s in t₀..τ, hbar s) (h t) I t := by
    rw [← hbar_eq t ht']
    exact hD.hasDerivWithinAt
  refine hD'.congr_of_eventuallyEq ?_ ?_
  · refine Filter.eventuallyEq_of_mem hnhds' fun τ hτ => ?_
    refine intervalIntegral.integral_congr fun s hs => ?_
    have : uIcc t₀ τ ⊆ Icc a' b' := uIcc_subset_Icc ht₀' hτ
    exact (hbar_eq s (this hs)).symm
  · refine intervalIntegral.integral_congr fun s hs => ?_
    have : uIcc t₀ t ⊆ Icc a' b' := uIcc_subset_Icc ht₀' ht'
    exact (hbar_eq s (this hs)).symm


/-- A bound for the Lipschitz constant of `x ↦ A s x` on a compact interval. -/
lemma lip_bound {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b, LipschitzWith K (fun x : Fin n → ℝ => A s *ᵥ x) := by
  have hc : ContinuousOn (fun s => ‖mvCLM (A s)‖) (Icc a b) :=
    (continuous_mvCLM.comp_continuousOn hA).norm
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc
  refine ⟨K.toNNReal, fun s hs => ?_⟩
  have h1 : ‖mvCLM (A s)‖₊ ≤ K.toNNReal := by
    have := hK s hs
    rw [Real.norm_eq_abs, abs_norm] at this
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact this.trans (le_max_left _ _)
  have h2 := (mvCLM (A s)).lipschitz
  have h3 : (⇑(mvCLM (A s)) : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => A s *ᵥ x :=
    funext (mvCLM_apply _)
  rw [h3] at h2
  exact h2.weaken h1

/-- Uniqueness for the linear system `ẋ = A(t) x` on an order-connected set `I`. -/
lemma lin_unique {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {f g : ℝ → Fin n → ℝ}
    (hf : ∀ s ∈ I, HasDerivWithinAt f (A s *ᵥ f s) I s)
    (hg : ∀ s ∈ I, HasDerivWithinAt g (A s *ᵥ g s) I s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (h0 : f t₀ = g t₀) : f t = g t := by
  rcases le_total t₀ t with hle | hle
  · have hJI : Icc t₀ t ⊆ I := hI.out ht₀ ht
    obtain ⟨K, hK⟩ := lip_bound (hA.mono hJI)
    have hfc : ContinuousOn f (Icc t₀ t) := fun s hs => (hf s (hJI hs)).continuousWithinAt.mono hJI
    have hgc : ContinuousOn g (Icc t₀ t) := fun s hs => (hg s (hJI hs)).continuousWithinAt.mono hJI
    have hnhds : ∀ s ∈ Ico t₀ t, Icc t₀ t ∈ 𝓝[≥] s := by
      intro s hs
      exact mem_nhdsGE_iff_exists_Icc_subset.2
        ⟨t, hs.2, Icc_subset_Icc hs.1 le_rfl⟩
    have key := ODE_solution_unique_of_mem_Icc_right (v := fun s x => A s *ᵥ x)
      (s := fun _ => univ) (K := K) (f := f) (g := g) (a := t₀) (b := t)
      (fun s hs => (hK s ⟨hs.1, hs.2.le⟩).lipschitzOnWith) hfc
      (fun s hs => ((hf s (hJI ⟨hs.1, hs.2.le⟩)).mono hJI).mono_of_mem_nhdsWithin (hnhds s hs))
      (fun _ _ => mem_univ _) hgc
      (fun s hs => ((hg s (hJI ⟨hs.1, hs.2.le⟩)).mono hJI).mono_of_mem_nhdsWithin (hnhds s hs))
      (fun _ _ => mem_univ _) h0
    exact key ⟨hle, le_rfl⟩
  · have hJI : Icc t t₀ ⊆ I := hI.out ht ht₀
    obtain ⟨K, hK⟩ := lip_bound (hA.mono hJI)
    have hfc : ContinuousOn f (Icc t t₀) := fun s hs => (hf s (hJI hs)).continuousWithinAt.mono hJI
    have hgc : ContinuousOn g (Icc t t₀) := fun s hs => (hg s (hJI hs)).continuousWithinAt.mono hJI
    have hnhds : ∀ s ∈ Ioc t t₀, Icc t t₀ ∈ 𝓝[≤] s := by
      intro s hs
      exact mem_nhdsLE_iff_exists_Icc_subset.2
        ⟨t, hs.1, Icc_subset_Icc le_rfl hs.2⟩
    have key := ODE_solution_unique_of_mem_Icc_left (v := fun s x => A s *ᵥ x)
      (s := fun _ => univ) (K := K) (f := f) (g := g) (a := t) (b := t₀)
      (fun s hs => (hK s ⟨hs.1.le, hs.2⟩).lipschitzOnWith) hfc
      (fun s hs => ((hf s (hJI ⟨hs.1.le, hs.2⟩)).mono hJI).mono_of_mem_nhdsWithin (hnhds s hs))
      (fun _ _ => mem_univ _) hgc
      (fun s hs => ((hg s (hJI ⟨hs.1.le, hs.2⟩)).mono hJI).mono_of_mem_nhdsWithin (hnhds s hs))
      (fun _ _ => mem_univ _) h0
    exact key ⟨le_rfl, hle⟩

/-- The cocycle identity `Φ(t, s) Φ(s, t₀) = Φ(t, t₀)` on `I`. -/
lemma cocycle_I {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t s t₀ : ℝ}
    (ht : t ∈ I) (hs : s ∈ I) (ht₀ : t₀ ∈ I) :
    Φ t s * Φ s t₀ = Φ t t₀ := by
  ext i j
  have key := lin_unique hI hA (f := fun τ k => (Φ τ s * Φ s t₀) k j)
    (g := fun τ k => Φ τ t₀ k j) ?_ ?_ hs ht ?_
  · exact congrFun key i
  · intro τ hτ
    rw [hasDerivWithinAt_pi]
    intro k
    have hd : HasDerivWithinAt (fun τ' => ∑ l, Φ τ' s k l * Φ s t₀ l j)
        (∑ l, (A τ * Φ τ s) k l * Φ s t₀ l j) I τ := by
      refine HasDerivWithinAt.fun_sum fun l _ => ?_
      exact ((hΦ s hs).2 τ hτ k l).mul_const _
    have e : (∑ l, (A τ * Φ τ s) k l * Φ s t₀ l j) =
        (A τ *ᵥ fun k => (Φ τ s * Φ s t₀) k j) k := by
      rw [← Matrix.mul_apply, Matrix.mul_assoc]; rfl
    exact e ▸ hd
  · intro τ hτ
    rw [hasDerivWithinAt_pi]
    intro k
    have h := (hΦ t₀ ht₀).2 τ hτ k j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  · funext k
    simp only [(hΦ s hs).1, Matrix.one_mul]

lemma mul_inv_I {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t t₀ : ℝ}
    (ht : t ∈ I) (ht₀ : t₀ ∈ I) :
    Φ t t₀ * Φ t₀ t = 1 := by
  rw [cocycle_I hI hA hΦ ht ht₀ ht, (hΦ t ht).1]


lemma continuousOn_mulVec {n : ℕ} {S : Set ℝ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {v : ℝ → Fin n → ℝ} (hM : ContinuousOn M S) (hv : ContinuousOn v S) :
    ContinuousOn (fun s => M s *ᵥ v s) S := by
  refine continuousOn_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (continuousOn_pi.1 (continuousOn_pi.1 hM i) k).mul (continuousOn_pi.1 hv k)

/-- `s ↦ Φ(s, t₀)` is continuous on `I`. -/
lemma continuousOn_Phi {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ}
    {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    ContinuousOn (fun s => Φ s t₀) I := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  exact fun s hs => ((hΦ t₀ ht₀).2 s hs i j).continuousWithinAt

/-- `s ↦ Φ(t₀, s)` is continuous on `I`: it is the inverse of `s ↦ Φ(s, t₀)`. -/
lemma continuousOn_Phi_inv {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ}
    (hI : I.OrdConnected) (hA : ContinuousOn A I) {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    ContinuousOn (fun s => Φ t₀ s) I := by
  have hinv : ∀ s ∈ I, Φ t₀ s = (Φ s t₀)⁻¹ := fun s hs =>
    (Matrix.inv_eq_right_inv (mul_inv_I hI hA hΦ hs ht₀)).symm
  have hc : ContinuousOn (fun s => (Φ s t₀)⁻¹) I := by
    intro s hs
    have hdet : (Φ s t₀).det ≠ 0 := by
      have h := congrArg Matrix.det (mul_inv_I hI hA hΦ hs ht₀)
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact left_ne_zero_of_mul_eq_one h
    have h1 : ContinuousAt (Ring.inverse : ℝ → ℝ) (Φ s t₀).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    have h2 : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹)
        ((fun s => Φ s t₀) s) := continuousAt_matrix_inv (Φ s t₀) h1
    exact ContinuousAt.comp_continuousWithinAt (g := fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹)
      (f := fun s => Φ s t₀) h2 (continuousOn_Phi hΦ ht₀ s hs)
  exact hc.congr hinv


/-- Pulling `Φ(τ, t₀)` out of the integral. -/
lemma voc_formula {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {g : ℝ → Fin n → ℝ} (hg : ContinuousOn g I)
    {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (x₀ : Fin n → ℝ) {τ : ℝ} (hτ : τ ∈ I) :
    Φ τ t₀ *ᵥ x₀ + ∫ s in t₀..τ, Φ τ s *ᵥ g s =
      Φ τ t₀ *ᵥ (x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s) := by
  have hcont : ContinuousOn (fun s => Φ t₀ s *ᵥ g s) I :=
    continuousOn_mulVec (continuousOn_Phi_inv hI hA hΦ ht₀) hg
  have hint : IntervalIntegrable (fun s => Φ t₀ s *ᵥ g s) MeasureTheory.volume t₀ τ :=
    (hcont.mono (hI.uIcc_subset ht₀ hτ)).intervalIntegrable
  have h1 : ∫ s in t₀..τ, Φ τ s *ᵥ g s = ∫ s in t₀..τ, mvCLM (Φ τ t₀) (Φ t₀ s *ᵥ g s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsI : s ∈ I := hI.uIcc_subset ht₀ hτ hs
    rw [mvCLM_apply, Matrix.mulVec_mulVec, cocycle_I hI hA hΦ hτ ht₀ hsI]
  rw [h1, ContinuousLinearMap.intervalIntegral_comp_comm (mvCLM (Φ τ t₀)) hint, mvCLM_apply,
    Matrix.mulVec_add]

/-- The candidate solution is differentiable within `I` with the right derivative. -/
lemma voc_deriv {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {g : ℝ → Fin n → ℝ} (hg : ContinuousOn g I)
    {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (x₀ : Fin n → ℝ) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun τ => Φ τ t₀ *ᵥ (x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s))
      (A t *ᵥ (Φ t t₀ *ᵥ (x₀ + ∫ s in t₀..t, Φ t₀ s *ᵥ g s)) + g t) I t := by
  have hcont : ContinuousOn (fun s => Φ t₀ s *ᵥ g s) I :=
    continuousOn_mulVec (continuousOn_Phi_inv hI hA hΦ ht₀) hg
  set F : ℝ → Fin n → ℝ := fun τ => x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s with hF
  have hFd : HasDerivWithinAt F (Φ t₀ t *ᵥ g t) I t :=
    (hasDerivWithinAt_integral hI hcont ht₀ ht).const_add x₀
  rw [hasDerivWithinAt_pi]
  intro i
  have hsum : HasDerivWithinAt (fun τ => ∑ k, Φ τ t₀ i k * F τ k)
      (∑ k, ((A t * Φ t t₀) i k * F t k + Φ t t₀ i k * (Φ t₀ t *ᵥ g t) k)) I t :=
    HasDerivWithinAt.fun_sum fun k _ =>
      ((hΦ t₀ ht₀).2 t ht i k).mul ((hasDerivWithinAt_pi.1 hFd) k)
  have e : (∑ k, ((A t * Φ t t₀) i k * F t k + Φ t t₀ i k * (Φ t₀ t *ᵥ g t) k)) =
      (A t *ᵥ (Φ t t₀ *ᵥ F t) + g t) i := by
    rw [Finset.sum_add_distrib]
    have e1 : ∑ k, (A t * Φ t t₀) i k * F t k = (A t *ᵥ (Φ t t₀ *ᵥ F t)) i := by
      rw [Matrix.mulVec_mulVec]; rfl
    have e2 : ∑ k, Φ t t₀ i k * (Φ t₀ t *ᵥ g t) k = g t i := by
      have : (Φ t t₀ *ᵥ (Φ t₀ t *ᵥ g t)) i = g t i := by
        rw [Matrix.mulVec_mulVec, mul_inv_I hI hA hΦ ht ht₀, Matrix.one_mulVec]
      exact this
    rw [e1, e2]; rfl
  exact e ▸ hsum

end VocAux

open VocAux in
theorem solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (g : ℝ → Fin n → ℝ) (hg : ContinuousOn g I)
    (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A I Φ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    (∀ t ∈ I, HasDerivWithinAt
        (fun τ => Matrix.mulVec (Φ τ t₀) x₀ + ∫ s in t₀..τ, Matrix.mulVec (Φ τ s) (g s))
        (Matrix.mulVec (A t) (Matrix.mulVec (Φ t t₀) x₀ +
          ∫ s in t₀..t, Matrix.mulVec (Φ t s) (g s)) + g t) I t) ∧
    (∀ y : ℝ → Fin n → ℝ,
      (∀ t ∈ I, HasDerivWithinAt y (Matrix.mulVec (A t) (y t) + g t) I t) → y t₀ = x₀ →
      ∀ t ∈ I, y t = Matrix.mulVec (Φ t t₀) x₀ + ∫ s in t₀..t, Matrix.mulVec (Φ t s) (g s)) := by
  have hform : ∀ τ ∈ I, Φ τ t₀ *ᵥ x₀ + ∫ s in t₀..τ, Φ τ s *ᵥ g s =
      Φ τ t₀ *ᵥ (x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s) := fun τ hτ =>
    voc_formula hI hA hg hΦ ht₀ x₀ hτ
  have hd : ∀ t ∈ I, HasDerivWithinAt
      (fun τ => Φ τ t₀ *ᵥ (x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s))
      (A t *ᵥ (Φ t t₀ *ᵥ (x₀ + ∫ s in t₀..t, Φ t₀ s *ᵥ g s)) + g t) I t := fun t ht =>
    voc_deriv hI hA hg hΦ ht₀ x₀ ht
  refine ⟨fun t ht => ?_, fun y hy hy0 t ht => ?_⟩
  · refine ((hd t ht).congr (fun τ hτ => hform τ hτ) (hform t ht)).congr_deriv ?_
    rw [hform t ht]
  · set xh : ℝ → Fin n → ℝ := fun τ => Φ τ t₀ *ᵥ (x₀ + ∫ s in t₀..τ, Φ t₀ s *ᵥ g s) with hxh
    have hz : ∀ s ∈ I, HasDerivWithinAt (fun τ => y τ - xh τ) (A s *ᵥ (y s - xh s)) I s := by
      intro s hs
      refine ((hy s hs).sub (hd s hs)).congr_deriv ?_
      rw [Matrix.mulVec_sub]
      abel
    have h0 : (fun τ => y τ - xh τ) t₀ = (fun _ : ℝ => (0 : Fin n → ℝ)) t₀ := by
      simp [hxh, hy0, (hΦ t₀ ht₀).1]
    have hk := lin_unique hI hA (f := fun τ => y τ - xh τ) (g := fun _ => (0 : Fin n → ℝ))
      hz (fun s _ => by simpa using hasDerivWithinAt_const s I (0 : Fin n → ℝ)) ht₀ ht h0
    have hyx : y t = xh t := sub_eq_zero.1 hk
    rw [hform t ht]
    exact hyx
