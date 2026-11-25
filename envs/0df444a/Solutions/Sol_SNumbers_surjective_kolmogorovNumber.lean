-- Prove2me | solution 1 for SNumbers.surjective_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:20.336654+00:00
-- url     : https://prove2.me/submissions/f48eeb60-afc3-4cf9-9edc-2fa13d6b67e9

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_kolmogorovNumber_comp_metricSurjection

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution :
    Surjective (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by
  intro W X Y _ _ _ _ _ _ S Q hQ n
  beta_reduce
  exact kolmogorovNumber_comp_metricSurjection hQ S n
end SNumbers
