-- Prove2me | solution 1 for PIW.ClassFinD.borelKGL_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:07.01395+00:00
-- url     : https://prove2.me/submissions/eb8d5090-4e88-4e17-bb38-6994dc9ae6f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Theorems.Thm_PIW_ClassFinD_glIncl_diagGL
import Theorems.Thm_PIW_ClassFinD_diag_eq_diagGL
import Theorems.Thm_PIW_ClassFinD_diagGL_mem_KGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain
namespace PIW.ClassFinD
theorem _root_.solution (hI : IwasawaAf) (hU : UnipApprox) (hC : IdeleClassFin) : BorelKGL := by
  classical
  intro F _ _ n
  obtain ⟨C, hCa⟩ := hC F
  refine ⟨(Fintype.piFinset fun _ : Fin n => C).image (diagGL n), fun x => ?_⟩
  obtain ⟨u, t, k, hu, ht, hk, rfl⟩ := hI F n x
  obtain ⟨ν, w, hw, huν⟩ := hU F n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose f c hc e he1 he2 hτ using fun i => hCa (τ i)
  have hsplit : diagGL n τ = glIncl F n (diagGL n f) * diagGL n c * diagGL n e := by
    rw [glIncl_diagGL, ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n),
      ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n)]
    congr 1
    funext i
    exact hτ i
  refine ⟨ν * diagGL n f, diagGL n c, Finset.mem_image.mpr ⟨c, Fintype.mem_piFinset.mpr hc, rfl⟩,
    diagGL n e * (w * k),
    (KGL F n).mul_mem (diagGL_mem_KGL F n e he1 he2) ((KGL F n).mul_mem hw hk), ?_⟩
  rw [huν, map_mul, hsplit]
  group
end PIW.ClassFinD
