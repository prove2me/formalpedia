-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussPoissonBound_proof_dfde059c4be9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:59.091007+00:00
-- url     : https://prove2.me/submissions/a9d6664c-b1cf-46d1-81fc-0e17d0643ded

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337
import Theorems.Thm_GroundTheory_Global_dualLattice_summable_norm
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_GroundTheory_Global_lattice_poisson_summation
import Theorems.Thm_GroundTheory_Global_lattice_summable_norm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open PGaussPoissonBound
namespace GroundTheory.Heights₂.Heights
namespace GaussPoissonBound
theorem _root_.solution (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by
  intro g B hB a
  obtain ⟨hdisc, hlat⟩ := hL g B hB
  have : DiscreteTopology (gaussLattice B) := hdisc
  have : IsZLattice ℝ (gaussLattice B) := hlat
  obtain ⟨hmem, hsurj, hinj⟩ := hK g B hB
  let E := EuclideanSpace ℝ (Fin g)
  let L := gaussLattice B
  let φ : (Fin g → ℤ) ≃ L := Equiv.ofBijective
    (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩)
    ⟨fun k k' h => hinj (by
        have := congrArg (fun x : L => WithLp.ofLp (x : E)) h
        simpa using this),
      fun x => by
        obtain ⟨k, hk⟩ := hsurj x x.2
        exact ⟨k, Subtype.ext hk.symm⟩⟩
  let G := GroundTheory.Global.gaussianSchwartz E
  let a' : E := WithLp.toLp 2 (B *ᵥ a)
  let f : (Fin g → ℤ) → ℝ := fun k =>
    Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))
  have hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ) := fun k => by
    have h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a)) := by
      rw [Matrix.mulVec_add]; rfl
    rw [h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]
  have hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k := fun k => by
    rw [hG, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
    funext fun x => GroundTheory.Global.gaussianSchwartz_apply x
  have hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ) := fun μ => by
    rw [hGfun]; exact hF g μ
  have hnD : ∀ μ : GroundTheory.Global.dualLattice L,
      ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2) := fun μ => by
    rw [norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]

  have hsumf : Summable f := by
    have h := (φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2
      (GroundTheory.Global.lattice_summable_norm L G a')
    exact h.congr fun k => hnG k

  have hsumD := GroundTheory.Global.dualLattice_summable_norm L G a'
  have hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2) :=
    hsumD.congr hnD
  refine ⟨hsumf, hsumE, ?_⟩

  have hP := GroundTheory.Global.lattice_poisson_summation L G a'
  have hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ) := by
    rw [← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]
    exact tsum_congr fun k => hG k
  rw [hlhs] at hP
  have hcov : ZLattice.covolume L = |B.det| := hV g B hB
  have hcpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  calc ∑' k, f k = ‖((∑' k, f k : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le)).symm
    _ = (ZLattice.covolume L)⁻¹ *
          ‖∑' μ : GroundTheory.Global.dualLattice L, 𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := by
        rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    _ ≤ (ZLattice.covolume L)⁻¹ *
          ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le
    _ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by
        rw [hcov]; exact congrArg _ (tsum_congr hnD)
end GaussPoissonBound
end GroundTheory.Heights₂.Heights
