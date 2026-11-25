-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.qc_leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:17.879222+00:00
-- url     : https://prove2.me/submissions/8ed43b5d-660a-4766-a470-214e73183cc6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCartier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution (ε : H →ₐ[K] K) (l : H →ₗ[K] K) (h1 : l 1 = 0) (h2 : ∀ y ∈ RingHom.ker ε ^ 2, l y = 0)
    (a b : H) : l (a * b) = ε a * l b + l a * ε b := by
  have ha : a - algebraMap K H (ε a) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hb : b - algebraMap K H (ε b) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hab : l ((a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))) = 0 :=
    h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
  have e : a * b = (a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) + ε a • b + ε b • a -
      (ε a * ε b) • (1 : H) := by
    simp only [Algebra.smul_def, map_mul, mul_one]
    ring
  rw [e, map_sub, map_add, map_add, hab, map_smul, map_smul, map_smul, h1]
  simp only [smul_eq_mul, mul_zero, sub_zero, zero_add]
  ring
end PositivityTheory.PrwZar.Qi
