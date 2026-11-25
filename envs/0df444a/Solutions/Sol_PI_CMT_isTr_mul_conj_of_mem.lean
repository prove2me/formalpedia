-- Prove2me | solution 1 for PI.CMT.isTr_mul_conj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:28.339702+00:00
-- url     : https://prove2.me/submissions/392af11a-573e-473f-81d6-e746eb8b757f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_conj_conj
import Theorems.Thm_PI_CMT_isTr_zero
import Theorems.Thm_PI_CMT_isTr_add
import Theorems.Thm_PI_CMT_conj_of_isTr
import Theorems.Thm_PI_CMT_isTr_mul_fixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
private theorem isTr_mul_conj_add_conj_mul (u v : 𝓞 K) :
    IsTr (u * conj v + conj u * v) :=
  ⟨u * conj v, by rw [map_mul, conj_conj]⟩
end PI.CMT
end
end

set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
namespace PI.CMT
theorem _root_.solution {u : 𝓞 K} (hu : u ∈ trIdeal K) : IsTr (u * conj u) := by
  have hu' : u ∈ Submodule.span (𝓞 K) {s : 𝓞 K | IsTr s} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem s hs =>
    have hfix : conj s = s := conj_of_isTr hs
    rw [hfix]
    exact isTr_mul_fixed hfix hs
  | zero =>
    rw [map_zero, mul_zero]
    exact isTr_zero
  | add x y _ _ hx hy =>
    have h := isTr_add (isTr_add hx hy) (isTr_mul_conj_add_conj_mul x y)
    rw [map_add]
    convert h using 1
    ring
  | smul a x _ hx =>
    have hb : conj (a * conj a) = a * conj a := by
      rw [map_mul, conj_conj, mul_comm]
    have h := isTr_mul_fixed hb hx
    rw [smul_eq_mul, map_mul]
    convert h using 1
    ring
end PI.CMT
