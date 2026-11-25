-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:25.958942+00:00
-- url     : https://prove2.me/submissions/888f3b9a-2e73-47c6-8320-0de6f2944455

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (T : Submonoid ℤ) (A : S) (L : AddSubgroup E)
    (hLA : ∀ a ∈ A, ∀ e ∈ L, a • e ∈ L) {ζ : Ω} (hζ : ζ ∈ A) {ι : Type*} [Fintype ι] (w : ι → E)
    (h : ∀ l, ∃ t ∈ T, ∃ n : ℕ, ((t : Ω) * ζ ^ n) • w l ∈ L) :
    ∃ t ∈ T, ∃ n : ℕ, ∀ l, ∀ n' ≥ n, ((t : Ω) * ζ ^ n') • w l ∈ L := by
  classical
  choose t ht n hn using h
  refine ⟨∏ l, t l, prod_mem fun l _ => ht l, Finset.univ.sup n, fun l n' hn' => ?_⟩
  have hle : n l ≤ n' := le_trans (Finset.le_sup (Finset.mem_univ l)) hn'
  have : (((∏ l, t l : ℤ) : Ω) * ζ ^ n') =
      (((∏ l' ∈ Finset.univ.erase l, t l' : ℤ) : Ω) * ζ ^ (n' - n l)) * ((t l : Ω) * ζ ^ n l) := by
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul,
      ← pow_sub_mul_pow ζ hle]
    ring
  rw [this, mul_smul]
  exact hLA _ (mul_mem (intCast_mem A _) (pow_mem hζ _)) _ (hn l)
end GroundTheory.Heights₂.Heights.Model
