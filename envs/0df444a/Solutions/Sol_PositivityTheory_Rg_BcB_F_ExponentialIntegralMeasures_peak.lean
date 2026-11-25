-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.peak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:01.227371+00:00
-- url     : https://prove2.me/submissions/521e6e4e-90fb-477f-adc1-a81e086b31c1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_restr
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_norm_le_of_chars
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_finite_cover
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_adjoin_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution {A : Type} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)]
    (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (p : A →⋆ₐ[ℂ] ℂ)
    (hβ : ∀ s g, Commute (β s) (R s g))
    (hne : ∀ s (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
      (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ = 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ g : A, p g = 1 ∧ ∀ s, ‖β s ^ m * R s g‖ ≤ ε := by
  classical
  let S : ∀ s, StarSubalgebra ℂ (H s →L[ℂ] H s) :=
    fun s => StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m})
  have hSc : ∀ s, ∀ x ∈ S s, ∀ y ∈ S s, x * y = y * x := fun s => adjoin_comm (R s) (β s) m (hβ s)
  have hR : ∀ s g, R s g ∈ S s := fun s g => StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)
  have hB : ∀ s, star (β s ^ m) * β s ^ m ∈ S s :=
    fun s => StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  let θ : ∀ s, (S s →⋆ₐ[ℂ] ℂ) → (A →⋆ₐ[ℂ] ℂ) :=
    fun s χ => χ.comp (StarAlgHom.codRestrict (R s) (S s) (hR s))
  have hθ : ∀ s χ g, θ s χ g = χ ⟨R s g, hR s g⟩ := fun _ _ _ => rfl
  set ε0 : ℝ := ε ^ 2 with hε0
  have hε0p : 0 < ε0 := by positivity
  let d : A → A := fun g => g - algebraMap ℂ A (p g)
  have hpd : ∀ g, p (d g) = 0 := by
    intro g; simp only [d, map_sub]; rw [AlgHomClass.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hcov : ∀ s, ∃ t : Finset A, ∀ ψ : (S s).topologicalClosure →ₐ[ℂ] ℂ,
      ε0 ≤ ‖ψ (StarSubalgebra.inclusion (S s).le_topologicalClosure ⟨_, hB s⟩)‖ →
        ∃ g ∈ t, 1 < ‖ψ (StarSubalgebra.inclusion (S s).le_topologicalClosure ⟨_, hR s (d g)⟩)‖ := by
    intro s
    apply finite_cover (S s) (hSc s) (fun g => R s (d g)) (fun g => hR s (d g)) _ (hB s) ε0
    intro ψ hψ
    by_contra hno
    push_neg at hno
    obtain ⟨χ, hχb, hχ⟩ := restr (S s) (hSc s) ψ
    have hz : ∀ g, θ s χ (d g) = 0 := by
      intro g
      by_contra hz
      have h2 := hno ((2 / θ s χ (d g)) • g)
      rw [← hχ, ← hθ] at h2
      have hd : d ((2 / θ s χ (d g)) • g) = (2 / θ s χ (d g)) • d g := by
        simp only [d, map_smul, smul_sub, smul_eq_mul, Algebra.algebraMap_eq_smul_one, smul_smul]
      rw [hd, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz] at h2
      norm_num at h2
    have hp : ∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g := by
      intro g
      have := hz g
      rw [show d g = g - algebraMap ℂ A (p g) from rfl, map_sub, AlgHomClass.commutes] at this
      rw [← hθ]
      simpa [sub_eq_zero] using this
    have h0 := hne s χ hχb hp
    rw [← hχ] at hψ
    rw [h0, norm_zero] at hψ
    linarith
  choose t ht using hcov
  set h : A := ∑ s, ∑ g ∈ t s, star (d g) * d g with hh
  have hph : p h = 0 := by simp [hh, map_sum, map_mul, map_star, hpd]
  set M : ℝ := 2 + ∑ s, ‖R s h‖ with hM
  have hM2 : ∀ s, ‖R s h‖ + 2 ≤ M := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖R s h‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
    linarith
  have hMpos : 0 < M := by have := hM2 (Classical.arbitrary ι); linarith [norm_nonneg (R (Classical.arbitrary ι) h)]
  set b0 : ℝ := 1 + ∑ s, ‖star (β s ^ m) * β s ^ m‖ with hb0
  have hb0s : ∀ s, ‖star (β s ^ m) * β s ^ m‖ ≤ b0 := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖star (β s ^ m) * β s ^ m‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ s)
    linarith
  have hb0p : 0 < b0 := by positivity
  set q : ℝ := 1 - 1 / M with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hMpos]
    have := hM2 (Classical.arbitrary ι); linarith [norm_nonneg (R (Classical.arbitrary ι) h)]
  have hq1 : q < 1 := by rw [hq]; have : 0 < 1 / M := by positivity
                         linarith
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (div_pos hε0p hb0p) hq1
  refine ⟨(1 - ((M : ℂ)⁻¹) • h) ^ L, by simp [map_pow, map_sub, hph], fun s => ?_⟩
  set g : A := (1 - ((M : ℂ)⁻¹) • h) ^ L with hg
  set B := star (β s ^ m) * β s ^ m with hBdef
  have hx : R s (star g) * B * R s g ∈ S s :=
    mul_mem (mul_mem (hR s _) (hB s)) (hR s g)
  have hkey : ‖R s (star g) * B * R s g‖ ≤ ε0 := by
    apply norm_le_of_chars (S s) (hSc s) _ hx ε0 hε0p.le
    intro ψ
    obtain ⟨χ, hχb, hχ⟩ := restr (S s) (hSc s) ψ
    rw [← hχ]
    have hsplit : (⟨R s (star g) * B * R s g, hx⟩ : S s) =
        ⟨R s (star g), hR s _⟩ * ⟨B, hB s⟩ * ⟨R s g, hR s g⟩ := rfl
    rw [hsplit, map_mul, map_mul, ← hθ, ← hθ, map_star]

    set w := θ s χ g
    set T : ℝ := ∑ s', ∑ g' ∈ t s', ‖θ s χ (d g')‖ ^ 2 with hT
    have hTh : θ s χ h = (T : ℂ) := by
      simp only [hh, hT, map_sum, map_mul, map_star, Complex.star_def, Complex.conj_mul']
      push_cast; rfl
    have hT0 : 0 ≤ T := by positivity
    have hTM : T + 2 ≤ M := by
      have h1 : ‖θ s χ h‖ ≤ ‖R s h‖ := by rw [hθ]; exact hχb _
      rw [hTh, Complex.norm_real, Real.norm_of_nonneg hT0] at h1
      linarith [hM2 s]
    have hw : w = ((1 - T / M : ℝ) : ℂ) ^ L := by
      simp only [w, hg, map_pow, map_sub, map_one, map_smul, hTh, smul_eq_mul]
      push_cast; ring
    have hwn : ‖w‖ = (1 - T / M) ^ L := by
      rw [hw, norm_pow, Complex.norm_real, Real.norm_of_nonneg]
      rw [sub_nonneg, div_le_one hMpos]; linarith
    have hw1 : ‖w‖ ≤ 1 := by
      rw [hwn]; apply pow_le_one₀
      · rw [sub_nonneg, div_le_one hMpos]; linarith
      · have : 0 ≤ T / M := by positivity
        linarith
    have hχB : ‖χ ⟨B, hB s⟩‖ ≤ b0 := (hχb _).trans (hb0s s)
    rw [norm_mul, norm_mul, norm_star]
    by_cases hbig : ε0 ≤ ‖χ ⟨B, hB s⟩‖
    · obtain ⟨g', hg't, hg'⟩ := ht s ψ (by rw [← hχ]; exact hbig)
      rw [← hχ, ← hθ] at hg'
      have hT1 : 1 < T := by
        have a1 : ‖θ s χ (d g')‖ ^ 2 ≤ ∑ g'' ∈ t s, ‖θ s χ (d g'')‖ ^ 2 :=
          Finset.single_le_sum (f := fun g'' => ‖θ s χ (d g'')‖ ^ 2) (fun _ _ => by positivity) hg't
        have a2 : ∑ g'' ∈ t s, ‖θ s χ (d g'')‖ ^ 2 ≤ T :=
          Finset.single_le_sum (f := fun s' => ∑ g'' ∈ t s', ‖θ s χ (d g'')‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ s)
        nlinarith
      have hwq : ‖w‖ ≤ q ^ L := by
        rw [hwn]; apply pow_le_pow_left₀
        · rw [sub_nonneg, div_le_one hMpos]; linarith
        · rw [hq]; have : 1 / M ≤ T / M := div_le_div_of_nonneg_right hT1.le hMpos.le
          linarith
      calc ‖w‖ * ‖χ ⟨B, hB s⟩‖ * ‖w‖ ≤ 1 * b0 * q ^ L := by
            apply mul_le_mul (mul_le_mul hw1 hχB (norm_nonneg _) zero_le_one) hwq (norm_nonneg _)
              (by positivity)
        _ ≤ ε0 := by
            have := (lt_div_iff₀ hb0p).1 hL
            nlinarith
    · push_neg at hbig
      calc ‖w‖ * ‖χ ⟨B, hB s⟩‖ * ‖w‖ ≤ 1 * ε0 * 1 := by
            apply mul_le_mul (mul_le_mul hw1 hbig.le (norm_nonneg _) zero_le_one) hw1 (norm_nonneg _)
              (by positivity)
        _ = ε0 := by ring
  have hsq : ‖β s ^ m * R s g‖ ^ 2 ≤ ε ^ 2 := by
    have e1 : star (β s ^ m * R s g) * (β s ^ m * R s g) = R s (star g) * B * R s g := by
      rw [star_mul, map_star, hBdef]; noncomm_ring
    rw [sq, ← CStarRing.norm_star_mul_self, e1]
    exact hkey
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (β s ^ m * R s g)]
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
