-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.homog_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:43.545104+00:00
-- url     : https://prove2.me/submissions/5693b4aa-943d-4b92-bc50-2b3652ea3d59

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
import Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_of_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {P : TRep R G} (e : ∀ n, P.coch.X n ≃ₗ[R] hcoch P G n)
    (h1 : ∀ n f x, (e n f).1 x = P.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) (n : ℕ)
    (f : P.coch.X n) (F : (Fin (n + 1) → G) → P.V) (hF : F ∈ hcoch P G n)
    (hf : ∀ g, f.1 g = F (Fin.partialProd g)) : (e n f).1 = F := by
  funext x
  rw [h1, hf]
  have ht : (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun i : Fin n => ((x 0)⁻¹ * x i.castSucc)⁻¹ * ((x 0)⁻¹ * x i.succ) := by
    funext i
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hp : Fin.partialProd (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun k => (x 0)⁻¹ * x k := by
    funext k
    rw [ht]
    exact pp_of_one (fun k => (x 0)⁻¹ * x k) (inv_mul_cancel _) k
  rw [hp]
  simp only [hcoch] at hF
  have h2 := hF.2 (x 0) (fun k => (x 0)⁻¹ * x k)
  simp only [smul_eq_mul, mul_inv_cancel_left] at h2
  exact h2.symm
end ReciprocityTheory.Coh.CCA
