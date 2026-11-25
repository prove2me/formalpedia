-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:28.058083+00:00
-- url     : https://prove2.me/submissions/4a390475-a42e-4c15-a5ed-08802b0b5341

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_famC_mul
import Theorems.Thm_PI_Dv_ProjGramW_span_O_famC
import Theorems.Thm_PI_Dv_ProjGramW_idx_add
import Theorems.Thm_PI_Dv_ProjGramW_stdE_li
import Theorems.Thm_PI_Dv_ProjGramW_idx_reduce
import Theorems.Thm_PI_Dv_ProjGramW_li_famC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C1 C2 : Matrix (Fin d) (Fin d) K)
    (h1 : C1.det ≠ 0) (h2 : C2.det ≠ 0) : idxStd w (C1 * C2) = idxStd w C1 + idxStd w C2 := by
  have h12 : (C1 * C2).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h1 h2
  have hEfg : (Submodule.span (𝓞 K) (Set.range (stdE (K := K) d))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hN1fg : (Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) C1))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hN12fg : (Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (C1 * C2)))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hs1 := (span_O_famC (V := Fin d →₀ K) (stdE (K := K) d) C1 h1).symm
  have hs12 : Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (C1 * C2))) :
        Submodule (𝓞 K) (Fin d →₀ K)) : Set (Fin d →₀ K)) =
      Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) C1)) :
        Submodule (𝓞 K) (Fin d →₀ K)) : Set (Fin d →₀ K)) := by
    rw [span_O_famC _ _ h12, span_O_famC _ _ h1]
  have hadd := idx_add (V := Fin d →₀ K) hI w hEfg hN1fg hN12fg hs1 hs12
  have hli : LinearIndependent K (famC (stdE (K := K) d) C1) := li_famC (V := Fin d →₀ K) (stdE_li d) C1 h1
  have hr := idx_reduce hI w hli C2 h2
  rw [famC_mul] at hr
  unfold idxStd
  rw [hadd, hr]
  rfl
end PI.Dv.ProjGramW
