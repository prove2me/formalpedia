-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:31:53.273734+00:00
-- url     : https://prove2.me/submissions/c4559cf4-2db3-4088-968b-fd1817b8399f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_ampleRing_ca2e319bb849
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hL : IsVeryAmpleBy L h)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I) {l : Fin (r₁ + 1)}
    {j : Fin (s₁ + 1)} (hl : h l ≠ 0) (hj : g j ≠ 0) {B : Subalgebra k Ω}
    (hB : ∀ a b, h a * g b / (h l * g j) ∈ B) {z : Ω}
    (hz : z ∈ ampleRing (L.twist G) 1 (h l * g j)) : z ∈ B := by
  obtain ⟨n, A, Bv, JJ, hA, hBv, hsum, hcov⟩ := hL.affine l hl
  have hK : ∀ y ∈ ampleRing L 1 (h l), y ∈ B := by
    intro y hy
    refine Algebra.adjoin_le ?_ (hL.closed l hl hy)
    rintro _ ⟨a, rfl⟩
    show h a / h l ∈ B
    have h10 : h a / h l = h a * g j / (h l * g j) := (mul_div_mul_right _ _ hj).symm
    rw [h10]
    exact hB a j
  refine mem_of_pow_mul_mem (fun i => hK _ (hA i)) (fun i => hK _ (hBv i)) hsum fun i => ?_
  obtain ⟨m, hm⟩ := Set.mem_iInter.mp hz (JJ i)
  rw [one_mul, SubSystem.pow_sub_eq_pow, SubSystem.twist_sub_eq_mul, ← hL.generates (JJ i),
    ← hgg (JJ i), Submodule.span_mul_span, Submodule.span_pow] at hm
  refine exists_pow_mul_mem_of_mem_span (mul_ne_zero hl hj) (hK _ (hBv i))
    (div_pow_mem_of_mem_pow (fun y hy => ?_) m) (fun c hc => ?_) hm
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
    exact hB a b
  · obtain ⟨E, hE⟩ := exists_pow_mul_mem_ampleRing (hBv i) (hcov i) hc
    exact ⟨E, hK _ hE⟩
end GroundTheory.Heights₂.Heights.Kleiman
