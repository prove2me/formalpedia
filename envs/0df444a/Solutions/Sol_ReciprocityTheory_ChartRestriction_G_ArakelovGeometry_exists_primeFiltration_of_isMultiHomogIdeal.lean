-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_primeFiltration_of_isMultiHomogIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:38.327132+00:00
-- url     : https://prove2.me/submissions/d8ed1701-12b0-4880-aa9d-018fee13fd0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_colon_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
