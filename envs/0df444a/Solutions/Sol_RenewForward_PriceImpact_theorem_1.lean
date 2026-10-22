-- Prove2me | solution 1 for RenewForward.PriceImpact.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:44:08.768087+00:00
-- url     : https://prove2.me/submissions/209aab6d-e23a-4b39-a543-d78a4d90dbd8

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

open MeasureTheory ProbabilityTheory RenewForward.PriceImpact

namespace RFT1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `i`-th raw moment. -/
noncomputable def mom (P : Measure Ω) (f : Ω → ℝ) (i : ℕ) : ℝ := ∫ w, f w ^ i ∂P

theorem bdd_fun (P : Measure Ω) [IsProbabilityMeasure P] {θ ξ : Ω → ℝ} (hθm : Measurable θ)
    (hξm : Measurable ξ) {lo hi : ℝ} (hθb : ∀ w, θ w ∈ Set.Icc lo hi)
    (hξb : ∀ w, ξ w ∈ Set.Icc (0:ℝ) 1) (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun w => g (θ w, ξ w)) P ∧ MemLp (fun w => g (θ w, ξ w)) 2 P := by
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hm : AEStronglyMeasurable (fun w => g (θ w, ξ w)) P :=
    (hg.measurable.comp (hθm.prodMk hξm)).aestronglyMeasurable
  have hb : ∀ᵐ w ∂P, ‖g (θ w, ξ w)‖ ≤ C := ae_of_all _ (fun w => hC _ ⟨hθb w, hξb w⟩)
  exact ⟨Integrable.of_bound hm C hb, MemLp.of_bound hm C hb⟩

theorem Epoly (P : Measure Ω) [IsProbabilityMeasure P] {θ ξ : Ω → ℝ} (hθm : Measurable θ)
    (hξm : Measurable ξ) {lo hi : ℝ} (hθb : ∀ w, θ w ∈ Set.Icc lo hi)
    (hξb : ∀ w, ξ w ∈ Set.Icc (0:ℝ) 1) (hind : IndepFun θ ξ P) (c : Fin 5 → Fin 5 → ℝ)
    (f : Ω → ℝ) (hf : ∀ w, f w = ∑ i : Fin 5, ∑ j : Fin 5, c i j * (θ w ^ (i:ℕ) * ξ w ^ (j:ℕ))) :
    ∫ w, f w ∂P = ∑ i : Fin 5, ∑ j : Fin 5, c i j * (mom P θ i * mom P ξ j) := by
  have hint : ∀ i j : Fin 5, Integrable (fun w => c i j * (θ w ^ (i:ℕ) * ξ w ^ (j:ℕ))) P :=
    fun i j => (bdd_fun P hθm hξm hθb hξb (fun p => c i j * (p.1 ^ (i:ℕ) * p.2 ^ (j:ℕ)))
      (by fun_prop)).1
  rw [integral_congr_ae (ae_of_all _ hf),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul]
  congr 1
  have hi := hind.comp (measurable_id.pow_const (i:ℕ)) (measurable_id.pow_const (j:ℕ))
  exact hi.integral_fun_mul_eq_mul_integral ((hθm.pow_const _).aestronglyMeasurable)
    ((hξm.pow_const _).aestronglyMeasurable)

theorem util_eq (M : Params) (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : MemLp f 2 P) :
    utility M P f = ∫ w, f w ∂P - M.lam / 2 * (∫ w, f w ^ 2 ∂P - (∫ w, f w ∂P) ^ 2) := by
  unfold utility; rw [variance_eq_sub hf]; rfl

theorem quad_max (g : ℝ → ℝ) (a b t : ℝ) (ha : 0 < a) (hg : ∀ s, g s = g 0 + b * s - a * s ^ 2) :
    (∀ s, g s ≤ g t) ↔ t = b / (2 * a) := by
  have key : ∀ s, g (b / (2 * a)) - g s = a * (s - b / (2 * a)) ^ 2 := by
    intro s; rw [hg s, hg (b / (2 * a))]; field_simp; ring
  constructor
  · intro h
    have h1 := h (b / (2 * a))
    have h2 := key t
    have : a * (t - b / (2 * a)) ^ 2 ≤ 0 := by linarith
    have : (t - b / (2 * a)) ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have : t - b / (2 * a) = 0 := by nlinarith [sq_nonneg (t - b / (2 * a))]
    linarith
  · intro ht s
    have := key s
    rw [← ht] at this
    nlinarith [sq_nonneg (s - t)]

noncomputable def MR (M : Params) (kW F pf fr : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(-F*fr/3 + M.a*fr/3 + 2*M.c*fr/3 - fr*pf), (-fr*kW/3), 0, 0, 0],
    ![(F*(M.NR:ℝ)⁻¹/3 - M.a*(M.NR:ℝ)⁻¹/3 - 2*M.c*(M.NR:ℝ)⁻¹/3 + fr/3 + (M.NR:ℝ)⁻¹*M.pR), ((M.NR:ℝ)⁻¹*kW/3), 0, 0, 0],
    ![(-(M.NR:ℝ)⁻¹/3), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MR2 (M : Params) (kW F pf fr : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(F^2*fr^2/9 - 2*F*M.a*fr^2/9 - 4*F*M.c*fr^2/9 + 2*F*fr^2*pf/3 + M.a^2*fr^2/9 + 4*M.a*M.c*fr^2/9 - 2*M.a*fr^2*pf/3 + 4*M.c^2*fr^2/9 - 4*M.c*fr^2*pf/3 + fr^2*pf^2), (2*F*fr^2*kW/9 - 2*M.a*fr^2*kW/9 - 4*M.c*fr^2*kW/9 + 2*fr^2*kW*pf/3), (fr^2*kW^2/9), 0, 0],
    ![(-2*F^2*fr*(M.NR:ℝ)⁻¹/9 + 4*F*M.a*fr*(M.NR:ℝ)⁻¹/9 + 8*F*M.c*fr*(M.NR:ℝ)⁻¹/9 - 2*F*fr^2/9 - 2*F*fr*(M.NR:ℝ)⁻¹*M.pR/3 - 2*F*fr*(M.NR:ℝ)⁻¹*pf/3 - 2*M.a^2*fr*(M.NR:ℝ)⁻¹/9 - 8*M.a*M.c*fr*(M.NR:ℝ)⁻¹/9 + 2*M.a*fr^2/9 + 2*M.a*fr*(M.NR:ℝ)⁻¹*M.pR/3 + 2*M.a*fr*(M.NR:ℝ)⁻¹*pf/3 - 8*M.c^2*fr*(M.NR:ℝ)⁻¹/9 + 4*M.c*fr^2/9 + 4*M.c*fr*(M.NR:ℝ)⁻¹*M.pR/3 + 4*M.c*fr*(M.NR:ℝ)⁻¹*pf/3 - 2*fr^2*pf/3 - 2*fr*(M.NR:ℝ)⁻¹*M.pR*pf), (-4*F*fr*(M.NR:ℝ)⁻¹*kW/9 + 4*M.a*fr*(M.NR:ℝ)⁻¹*kW/9 + 8*M.c*fr*(M.NR:ℝ)⁻¹*kW/9 - 2*fr^2*kW/9 - 2*fr*(M.NR:ℝ)⁻¹*kW*M.pR/3 - 2*fr*(M.NR:ℝ)⁻¹*kW*pf/3), (-2*fr*(M.NR:ℝ)⁻¹*kW^2/9), 0, 0],
    ![(F^2*(M.NR:ℝ)⁻¹^2/9 - 2*F*M.a*(M.NR:ℝ)⁻¹^2/9 - 4*F*M.c*(M.NR:ℝ)⁻¹^2/9 + 4*F*fr*(M.NR:ℝ)⁻¹/9 + 2*F*(M.NR:ℝ)⁻¹^2*M.pR/3 + M.a^2*(M.NR:ℝ)⁻¹^2/9 + 4*M.a*M.c*(M.NR:ℝ)⁻¹^2/9 - 4*M.a*fr*(M.NR:ℝ)⁻¹/9 - 2*M.a*(M.NR:ℝ)⁻¹^2*M.pR/3 + 4*M.c^2*(M.NR:ℝ)⁻¹^2/9 - 8*M.c*fr*(M.NR:ℝ)⁻¹/9 - 4*M.c*(M.NR:ℝ)⁻¹^2*M.pR/3 + fr^2/9 + 2*fr*(M.NR:ℝ)⁻¹*M.pR/3 + 2*fr*(M.NR:ℝ)⁻¹*pf/3 + (M.NR:ℝ)⁻¹^2*M.pR^2), (2*F*(M.NR:ℝ)⁻¹^2*kW/9 - 2*M.a*(M.NR:ℝ)⁻¹^2*kW/9 - 4*M.c*(M.NR:ℝ)⁻¹^2*kW/9 + 4*fr*(M.NR:ℝ)⁻¹*kW/9 + 2*(M.NR:ℝ)⁻¹^2*kW*M.pR/3), ((M.NR:ℝ)⁻¹^2*kW^2/9), 0, 0],
    ![(-2*F*(M.NR:ℝ)⁻¹^2/9 + 2*M.a*(M.NR:ℝ)⁻¹^2/9 + 4*M.c*(M.NR:ℝ)⁻¹^2/9 - 2*fr*(M.NR:ℝ)⁻¹/9 - 2*(M.NR:ℝ)⁻¹^2*M.pR/3), (-2*(M.NR:ℝ)⁻¹^2*kW/9), 0, 0, 0],
    ![((M.NR:ℝ)⁻¹^2/9), 0, 0, 0, 0]]

noncomputable def MP (M : Params) (kW fi fj pf : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(M.a^2/9 - 2*M.a*M.c/9 - 2*M.a*fi/9 - 2*M.a*fj/9 + M.c^2/9 - 7*M.c*fi/9 + 2*M.c*fj/9 + fi^2/9 + 2*fi*fj/9 + fi*pf + fj^2/9), (-2*M.a*kW/9 + 2*M.c*kW/9 + 2*fi*kW/9 + 2*fj*kW/9), (kW^2/9), 0, 0],
    ![(2*M.a/9 - 2*M.c/9 - 2*fi/9 - 2*fj/9), (-2*kW/9), 0, 0, 0],
    ![(1/9), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MP2 (M : Params) (kW fi fj pf : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(M.a^4/81 - 4*M.a^3*M.c/81 - 4*M.a^3*fi/81 - 4*M.a^3*fj/81 + 2*M.a^2*M.c^2/27 - 2*M.a^2*M.c*fi/27 + 4*M.a^2*M.c*fj/27 + 2*M.a^2*fi^2/27 + 4*M.a^2*fi*fj/27 + 2*M.a^2*fi*pf/9 + 2*M.a^2*fj^2/27 - 4*M.a*M.c^3/81 + 8*M.a*M.c^2*fi/27 - 4*M.a*M.c^2*fj/27 + 8*M.a*M.c*fi^2/27 + 4*M.a*M.c*fi*fj/27 - 4*M.a*M.c*fi*pf/9 - 4*M.a*M.c*fj^2/27 - 4*M.a*fi^3/81 - 4*M.a*fi^2*fj/27 - 4*M.a*fi^2*pf/9 - 4*M.a*fi*fj^2/27 - 4*M.a*fi*fj*pf/9 - 4*M.a*fj^3/81 + M.c^4/81 - 14*M.c^3*fi/81 + 4*M.c^3*fj/81 + 17*M.c^2*fi^2/27 - 8*M.c^2*fi*fj/27 + 2*M.c^2*fi*pf/9 + 2*M.c^2*fj^2/27 - 14*M.c*fi^3/81 - 8*M.c*fi^2*fj/27 - 14*M.c*fi^2*pf/9 - 2*M.c*fi*fj^2/27 + 4*M.c*fi*fj*pf/9 + 4*M.c*fj^3/81 + fi^4/81 + 4*fi^3*fj/81 + 2*fi^3*pf/9 + 2*fi^2*fj^2/27 + 4*fi^2*fj*pf/9 + fi^2*pf^2 + 4*fi*fj^3/81 + 2*fi*fj^2*pf/9 + fj^4/81), (-4*M.a^3*kW/81 + 4*M.a^2*M.c*kW/27 + 4*M.a^2*fi*kW/27 + 4*M.a^2*fj*kW/27 - 4*M.a*M.c^2*kW/27 + 4*M.a*M.c*fi*kW/27 - 8*M.a*M.c*fj*kW/27 - 4*M.a*fi^2*kW/27 - 8*M.a*fi*fj*kW/27 - 4*M.a*fi*kW*pf/9 - 4*M.a*fj^2*kW/27 + 4*M.c^3*kW/81 - 8*M.c^2*fi*kW/27 + 4*M.c^2*fj*kW/27 - 8*M.c*fi^2*kW/27 - 4*M.c*fi*fj*kW/27 + 4*M.c*fi*kW*pf/9 + 4*M.c*fj^2*kW/27 + 4*fi^3*kW/81 + 4*fi^2*fj*kW/27 + 4*fi^2*kW*pf/9 + 4*fi*fj^2*kW/27 + 4*fi*fj*kW*pf/9 + 4*fj^3*kW/81), (2*M.a^2*kW^2/27 - 4*M.a*M.c*kW^2/27 - 4*M.a*fi*kW^2/27 - 4*M.a*fj*kW^2/27 + 2*M.c^2*kW^2/27 - 2*M.c*fi*kW^2/27 + 4*M.c*fj*kW^2/27 + 2*fi^2*kW^2/27 + 4*fi*fj*kW^2/27 + 2*fi*kW^2*pf/9 + 2*fj^2*kW^2/27), (-4*M.a*kW^3/81 + 4*M.c*kW^3/81 + 4*fi*kW^3/81 + 4*fj*kW^3/81), (kW^4/81)],
    ![(4*M.a^3/81 - 4*M.a^2*M.c/27 - 4*M.a^2*fi/27 - 4*M.a^2*fj/27 + 4*M.a*M.c^2/27 - 4*M.a*M.c*fi/27 + 8*M.a*M.c*fj/27 + 4*M.a*fi^2/27 + 8*M.a*fi*fj/27 + 4*M.a*fi*pf/9 + 4*M.a*fj^2/27 - 4*M.c^3/81 + 8*M.c^2*fi/27 - 4*M.c^2*fj/27 + 8*M.c*fi^2/27 + 4*M.c*fi*fj/27 - 4*M.c*fi*pf/9 - 4*M.c*fj^2/27 - 4*fi^3/81 - 4*fi^2*fj/27 - 4*fi^2*pf/9 - 4*fi*fj^2/27 - 4*fi*fj*pf/9 - 4*fj^3/81), (-4*M.a^2*kW/27 + 8*M.a*M.c*kW/27 + 8*M.a*fi*kW/27 + 8*M.a*fj*kW/27 - 4*M.c^2*kW/27 + 4*M.c*fi*kW/27 - 8*M.c*fj*kW/27 - 4*fi^2*kW/27 - 8*fi*fj*kW/27 - 4*fi*kW*pf/9 - 4*fj^2*kW/27), (4*M.a*kW^2/27 - 4*M.c*kW^2/27 - 4*fi*kW^2/27 - 4*fj*kW^2/27), (-4*kW^3/81), 0],
    ![(2*M.a^2/27 - 4*M.a*M.c/27 - 4*M.a*fi/27 - 4*M.a*fj/27 + 2*M.c^2/27 - 2*M.c*fi/27 + 4*M.c*fj/27 + 2*fi^2/27 + 4*fi*fj/27 + 2*fi*pf/9 + 2*fj^2/27), (-4*M.a*kW/27 + 4*M.c*kW/27 + 4*fi*kW/27 + 4*fj*kW/27), (2*kW^2/27), 0, 0],
    ![(4*M.a/81 - 4*M.c/81 - 4*fi/81 - 4*fj/81), (-4*kW/81), 0, 0, 0],
    ![(1/81), 0, 0, 0, 0]]

noncomputable def MS (M : Params) (kW F : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(-F/3 + M.a/3 + 2*M.c/3), (-kW/3), 0, 0, 0],
    ![(1/3), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MS2 (M : Params) (kW F : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(F^2/9 - 2*F*M.a/9 - 4*F*M.c/9 + M.a^2/9 + 4*M.a*M.c/9 + 4*M.c^2/9), (2*F*kW/9 - 2*M.a*kW/9 - 4*M.c*kW/9), (kW^2/9), 0, 0],
    ![(-2*F/9 + 2*M.a/9 + 4*M.c/9), (-2*kW/9), 0, 0, 0],
    ![(1/9), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MY (M : Params) (kW F : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![0, 0, 0, 0, 0],
    ![(F*(M.NR:ℝ)⁻¹/3 - M.a*(M.NR:ℝ)⁻¹/3 - 2*M.c*(M.NR:ℝ)⁻¹/3 + (M.NR:ℝ)⁻¹*M.pR), ((M.NR:ℝ)⁻¹*kW/3), 0, 0, 0],
    ![(-(M.NR:ℝ)⁻¹/3), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MYS (M : Params) (kW F : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![0, 0, 0, 0, 0],
    ![(-F^2*(M.NR:ℝ)⁻¹/9 + 2*F*M.a*(M.NR:ℝ)⁻¹/9 + 4*F*M.c*(M.NR:ℝ)⁻¹/9 - F*(M.NR:ℝ)⁻¹*M.pR/3 - M.a^2*(M.NR:ℝ)⁻¹/9 - 4*M.a*M.c*(M.NR:ℝ)⁻¹/9 + M.a*(M.NR:ℝ)⁻¹*M.pR/3 - 4*M.c^2*(M.NR:ℝ)⁻¹/9 + 2*M.c*(M.NR:ℝ)⁻¹*M.pR/3), (-2*F*(M.NR:ℝ)⁻¹*kW/9 + 2*M.a*(M.NR:ℝ)⁻¹*kW/9 + 4*M.c*(M.NR:ℝ)⁻¹*kW/9 - (M.NR:ℝ)⁻¹*kW*M.pR/3), (-(M.NR:ℝ)⁻¹*kW^2/9), 0, 0],
    ![(2*F*(M.NR:ℝ)⁻¹/9 - 2*M.a*(M.NR:ℝ)⁻¹/9 - 4*M.c*(M.NR:ℝ)⁻¹/9 + (M.NR:ℝ)⁻¹*M.pR/3), (2*(M.NR:ℝ)⁻¹*kW/9), 0, 0, 0],
    ![(-(M.NR:ℝ)⁻¹/9), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MT3 (mu : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(-mu^3), 0, 0, 0, 0],
    ![(3*mu^2), 0, 0, 0, 0],
    ![(-3*mu), 0, 0, 0, 0],
    ![(1), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

noncomputable def MX3 (mu : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![(-mu^3), (3*mu^2), (-3*mu), (1), 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

theorem mom_zero (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) : mom P f 0 = 1 := by
  simp [mom]

/-- The retailer's marginal-utility intercept (raw moments). -/
noncomputable def R1p (M : Params) (P : Measure Ω) (θ ξ : Ω → ℝ) (kW F : ℝ) : ℝ :=
  F*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 1)^2/9 - F*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 2)/9 - F/3 - M.a*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 1)^2/9 + M.a*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 2)/9 + M.a/3 - 2*M.c*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 1)^2/9 + 2*M.c*(M.NR:ℝ)⁻¹*M.lam*(mom P θ 2)/9 + 2*M.c/3 - (M.NR:ℝ)⁻¹*kW^2*M.lam*(mom P θ 1)*(mom P ξ 1)^2/9 + (M.NR:ℝ)⁻¹*kW^2*M.lam*(mom P θ 1)*(mom P ξ 2)/9 + (M.NR:ℝ)⁻¹*kW*M.lam*(mom P θ 1)^2*(mom P ξ 1)/9 - (M.NR:ℝ)⁻¹*kW*M.lam*(mom P θ 2)*(mom P ξ 1)/9 + (M.NR:ℝ)⁻¹*M.lam*M.pR*(mom P θ 1)^2/3 - (M.NR:ℝ)⁻¹*M.lam*M.pR*(mom P θ 2)/3 - (M.NR:ℝ)⁻¹*M.lam*(mom P θ 1)*(mom P θ 2)/9 + (M.NR:ℝ)⁻¹*M.lam*(mom P θ 3)/9 - kW*(mom P ξ 1)/3 + (mom P θ 1)/3

noncomputable def VS (P : Measure Ω) (θ ξ : Ω → ℝ) (kW : ℝ) : ℝ :=
  (mom P θ 2 - mom P θ 1 ^ 2 + kW ^ 2 * (mom P ξ 2 - mom P ξ 1 ^ 2)) / 9

noncomputable def dd (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  (2 * kW ^ 2 * M.lam * m.s2X + 2 * M.lam * m.s2T + 18) / 81
    + (9 * kW ^ 2 * M.lam * m.s2X + 18 * M.lam * m.s2T) * (M.NR : ℝ)⁻¹ / 81

noncomputable def HH1 (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  -(4 * kW ^ 2 * M.lam * m.s2X + 4 * M.lam * m.s2T + 9) / 81
    - (9 * kW ^ 2 * M.lam * m.s2X + 18 * M.lam * m.s2T) * (M.NR : ℝ)⁻¹ / 81

theorem memLp_of (P : Measure Ω) [IsProbabilityMeasure P] {θ ξ : Ω → ℝ} (hθm : Measurable θ)
    (hξm : Measurable ξ) {lo hi : ℝ} (hθb : ∀ w, θ w ∈ Set.Icc lo hi)
    (hξb : ∀ w, ξ w ∈ Set.Icc (0:ℝ) 1) (g : ℝ × ℝ → ℝ) (hg : Continuous g) (f : Ω → ℝ)
    (hf : ∀ w, f w = g (θ w, ξ w)) : MemLp f 2 P := by
  have : f = fun w => g (θ w, ξ w) := funext hf
  rw [this]; exact (bdd_fun P hθm hξm hθb hξb g hg).2

theorem main (M : Params) (P : Measure Ω) [IsProbabilityMeasure P]
    (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ) (kW : ℝ) :
    (∀ f1 f2 pf : ℝ, IsFwdEq M P θ ξ kW f1 f2 pf ↔
      f1 = fStar M (momentsOf P θ ξ) kW ∧ f2 = fStar M (momentsOf P θ ξ) kW ∧
        pf = aF M (momentsOf P θ ξ) kW
          - 2 * bF M (momentsOf P θ ξ) kW * omegaFwd M (momentsOf P θ ξ) kW
            / nuFwd M (momentsOf P θ ξ) kW) := by
  obtain ⟨hθm, hξm, hind, ⟨lo, hi, hθb⟩, hξb, hlam, hNR, hvT, hvX⟩ := hS
  set m := momentsOf P θ ξ with hm
  have hN : (1 : ℝ) ≤ M.NR := by exact_mod_cast hNR
  have hN0 : (0 : ℝ) < M.NR := by linarith
  have EP := Epoly P hθm hξm hθb hξb hind
  have ML := memLp_of P hθm hξm hθb hξb
  -- raw moments vs the central moments in 
  have hθ1 : m.muT = mom P θ 1 := by simp [m, momentsOf, muTheta, mean, mom]
  have hξ1 : m.muX = mom P ξ 1 := by simp [m, momentsOf, muXi, mean, mom]
  have hθ2 : m.s2T = mom P θ 2 - mom P θ 1 ^ 2 := by
    change variance θ P = _
    rw [variance_eq_sub (ML (fun p => p.1) (by fun_prop) θ (fun _ => rfl))]
    simp [mom]
  have hξ2 : m.s2X = mom P ξ 2 - mom P ξ 1 ^ 2 := by
    change variance ξ P = _
    rw [variance_eq_sub (ML (fun p => p.2) (by fun_prop) ξ (fun _ => rfl))]
    simp [mom]
  have hθ3 : m.tauT = mom P θ 3 - 3 * mom P θ 1 * mom P θ 2 + 2 * mom P θ 1 ^ 3 := by
    change ∫ w, (θ w - mean P θ) ^ 3 ∂P = _
    rw [EP (MT3 (mean P θ)) (fun w => (θ w - mean P θ) ^ 3) (fun w => by
      simp [MT3, Fin.sum_univ_five]; ring)]
    have : mean P θ = mom P θ 1 := by simp [mean, mom]
    simp [MT3, Fin.sum_univ_five, mom_zero, this]; ring
  have hξ3 : m.tauX = mom P ξ 3 - 3 * mom P ξ 1 * mom P ξ 2 + 2 * mom P ξ 1 ^ 3 := by
    change ∫ w, (ξ w - mean P ξ) ^ 3 ∂P = _
    rw [EP (MX3 (mean P ξ)) (fun w => (ξ w - mean P ξ) ^ 3) (fun w => by
      simp [MX3, Fin.sum_univ_five]; ring)]
    have : mean P ξ = mom P ξ 1 := by simp [mean, mom]
    simp [MX3, Fin.sum_univ_five, mom_zero, this]; ring
  have r1 : mom P θ 1 = m.muT := hθ1.symm
  have r2 : mom P θ 2 = m.s2T + m.muT ^ 2 := by rw [hθ2, hθ1]; ring
  have r3 : mom P θ 3 = m.tauT + 3 * m.muT * m.s2T + m.muT ^ 3 := by rw [hθ3, hθ1, hθ2]; ring
  have x1 : mom P ξ 1 = m.muX := hξ1.symm
  have x2 : mom P ξ 2 = m.s2X + m.muX ^ 2 := by rw [hξ2, hξ1]; ring
  have x3 : mom P ξ 3 = m.tauX + 3 * m.muX * m.s2X + m.muX ^ 3 := by rw [hξ3, hξ1, hξ2]; ring
  have hs2T : 0 < m.s2T := hvT
  have hs2X : 0 < m.s2X := hvX
  -- retailers
  have hVS : 0 < VS P θ ξ kW := by
    unfold VS; rw [← hθ2, ← hξ2]; positivity
  have hRu : ∀ F pf fr, utility M P (retailerProfit M θ ξ kW F pf fr)
      = utility M P (retailerProfit M θ ξ kW F pf 0) + (R1p M P θ ξ kW F - pf) * fr
        - M.lam / 2 * VS P θ ξ kW * fr ^ 2 := by
    intro F pf fr
    have mR : ∀ t, MemLp (retailerProfit M θ ξ kW F pf t) 2 P := fun t =>
      ML (fun p => M.pR * (p.1 / M.NR) - ((M.a + 2 * M.c + p.1 - p.2 * kW - F) / 3) * (p.1 / M.NR - t)
        - pf * t) (by fun_prop) _ (fun w => rfl)
    rw [util_eq M P _ (mR fr), util_eq M P _ (mR 0)]
    have e1 := EP (MR M kW F pf fr) (retailerProfit M θ ξ kW F pf fr) (fun w => by
      simp [MR, retailerProfit, spotP, p0, Fin.sum_univ_five]; ring)
    have e2 := EP (MR2 M kW F pf fr) (fun w => retailerProfit M θ ξ kW F pf fr w ^ 2) (fun w => by
      simp [MR2, retailerProfit, spotP, p0, Fin.sum_univ_five]; ring)
    have e3 := EP (MR M kW F pf 0) (retailerProfit M θ ξ kW F pf 0) (fun w => by
      simp [MR, retailerProfit, spotP, p0, Fin.sum_univ_five]; ring)
    have e4 := EP (MR2 M kW F pf 0) (fun w => retailerProfit M θ ξ kW F pf 0 w ^ 2) (fun w => by
      simp [MR2, retailerProfit, spotP, p0, Fin.sum_univ_five]; ring)
    try simp only at e2 e4
    rw [e1, e2, e3, e4]
    simp only [Fin.sum_univ_five, MR, MR2, R1p, VS]
    simp [mom_zero]
    ring
  have hRopt : ∀ F pf fr, IsRetailerOpt M P θ ξ kW F pf fr ↔
      fr = (R1p M P θ ξ kW F - pf) / (2 * (M.lam / 2 * VS P θ ξ kW)) := by
    intro F pf fr
    exact quad_max (fun s => utility M P (retailerProfit M θ ξ kW F pf s)) _ _ fr
      (by positivity) (fun s => hRu F pf s)
  have key : ∀ F, aF M m kW - bF M m kW * F
      = R1p M P θ ξ kW F - M.lam * VS P θ ξ kW * F * (M.NR : ℝ)⁻¹ := by
    intro F
    simp only [aF, bF, meanP0, R1p, VS, r1, r2, r3, x1, x2, x3]
    ring
  set PF : ℝ → ℝ := fun F => aF M m kW - bF M m kW * F with hPF
  have hClears : ∀ pf F, Clears M P θ ξ kW pf F ↔ pf = PF F := by
    intro pf F
    have hL : 0 < M.lam * VS P θ ξ kW := by positivity
    have alg : (M.NR : ℝ) * ((R1p M P θ ξ kW F - pf) / (2 * (M.lam / 2 * VS P θ ξ kW))) = F ↔
        pf = PF F := by
      simp only [hPF]
      rw [key F]
      have h2 : 2 * (M.lam / 2 * VS P θ ξ kW) = M.lam * VS P θ ξ kW := by ring
      rw [h2]
      constructor
      · intro h
        field_simp at h ⊢
        linarith
      · intro h
        rw [h]
        field_simp
        ring
    rw [← alg]
    constructor
    · rintro ⟨fR, hopt, hsum⟩
      have hall : ∀ i, fR i = (R1p M P θ ξ kW F - pf) / (2 * (M.lam / 2 * VS P θ ξ kW)) :=
        fun i => (hRopt F pf (fR i)).1 (hopt i)
      rw [Finset.sum_congr rfl (fun i _ => hall i)] at hsum
      simpa using hsum
    · intro h
      refine ⟨fun _ => (R1p M P θ ξ kW F - pf) / (2 * (M.lam / 2 * VS P θ ξ kW)),
        fun i => (hRopt F pf _).2 rfl, ?_⟩
      simpa using h
  -- producers
  have hPu : ∀ t fj, utility M P (producerProfit M θ ξ kW t fj (PF (t + fj)))
      = utility M P (producerProfit M θ ξ kW 0 fj (PF (0 + fj)))
        + (omegaFwd M m kW / 81 + HH1 M m kW * fj) * t - dd M m kW * t ^ 2 := by
    intro t fj
    have mP : ∀ fi pf, MemLp (producerProfit M θ ξ kW fi fj pf) 2 P := fun fi pf =>
      ML (fun p => ((M.a + 2 * M.c + p.1 - p.2 * kW - (fi + fj)) / 3) *
          ((M.a - M.c + p.1 - p.2 * kW + 2 * fi - fj) / 3 - fi) + pf * fi
          - M.c * ((M.a - M.c + p.1 - p.2 * kW + 2 * fi - fj) / 3)) (by fun_prop) _ (fun w => rfl)
    rw [util_eq M P _ (mP _ _), util_eq M P _ (mP _ _)]
    have e1 := EP (MP M kW t fj (PF (t + fj))) (producerProfit M θ ξ kW t fj (PF (t + fj)))
      (fun w => by simp [MP, producerProfit, spotP, spotQ, p0, q0, Fin.sum_univ_five]; ring)
    have e2 := EP (MP2 M kW t fj (PF (t + fj)))
      (fun w => producerProfit M θ ξ kW t fj (PF (t + fj)) w ^ 2)
      (fun w => by simp [MP2, producerProfit, spotP, spotQ, p0, q0, Fin.sum_univ_five]; ring)
    have e3 := EP (MP M kW 0 fj (PF (0 + fj))) (producerProfit M θ ξ kW 0 fj (PF (0 + fj)))
      (fun w => by simp [MP, producerProfit, spotP, spotQ, p0, q0, Fin.sum_univ_five]; ring)
    have e4 := EP (MP2 M kW 0 fj (PF (0 + fj)))
      (fun w => producerProfit M θ ξ kW 0 fj (PF (0 + fj)) w ^ 2)
      (fun w => by simp [MP2, producerProfit, spotP, spotQ, p0, q0, Fin.sum_univ_five]; ring)
    rw [e1, e2, e3, e4]
    simp only [Fin.sum_univ_five, MP, MP2]
    simp [mom_zero]
    simp only [hPF, aF, bF, meanP0, omegaFwd, meanQ0, HH1, dd, r1, r2, r3, x1, x2, x3]
    ring
  have hdd : 0 < dd M m kW := by unfold dd; positivity
  have hbr : ∀ fi fj, (∀ f', utility M P (producerProfit M θ ξ kW f' fj (PF (f' + fj)))
        ≤ utility M P (producerProfit M θ ξ kW fi fj (PF (fi + fj)))) ↔
      fi = (omegaFwd M m kW / 81 + HH1 M m kW * fj) / (2 * dd M m kW) := fun fi fj =>
    quad_max (fun s => utility M P (producerProfit M θ ξ kW s fj (PF (s + fj)))) _ _ fi hdd
      (fun s => hPu s fj)
  have hEqv : ∀ f1 f2 pf, IsFwdEq M P θ ξ kW f1 f2 pf ↔
      pf = PF (f1 + f2) ∧ f1 = (omegaFwd M m kW / 81 + HH1 M m kW * f2) / (2 * dd M m kW) ∧
        f2 = (omegaFwd M m kW / 81 + HH1 M m kW * f1) / (2 * dd M m kW) := by
    intro f1 f2 pf
    constructor
    · rintro ⟨hc, h2, h3⟩
      have hpf := (hClears _ _).1 hc
      refine ⟨hpf, (hbr f1 f2).1 (fun f' => ?_), (hbr f2 f1).1 (fun f' => ?_)⟩
      · have := h2 f' (PF (f' + f2)) ((hClears _ _).2 rfl)
        rwa [hpf] at this
      · have := h3 f' (PF (f1 + f')) ((hClears _ _).2 rfl)
        rw [hpf, add_comm f1 f', add_comm f1 f2] at this
        exact this
    · rintro ⟨hpf, h1, h2⟩
      refine ⟨(hClears _ _).2 hpf, fun f' pf' hc => ?_, fun f' pf' hc => ?_⟩
      · rw [(hClears _ _).1 hc, hpf]
        exact (hbr f1 f2).2 h1 f'
      · rw [(hClears _ _).1 hc, hpf, add_comm f1 f', add_comm f1 f2]
        exact (hbr f2 f1).2 h2 f'
  have hnu : nuFwd M m kW = 81 * (2 * dd M m kW - HH1 M m kW) := by
    simp only [nuFwd, dd, HH1]; ring
  have hsum : 0 < 2 * dd M m kW + HH1 M m kW := by
    have : 2 * dd M m kW + HH1 M m kW
        = 27 / 81 + (9 * kW ^ 2 * M.lam * m.s2X + 18 * M.lam * m.s2T) * (M.NR : ℝ)⁻¹ / 81 := by
      simp only [dd, HH1]; ring
    rw [this]; positivity
  have hnupos : 0 < nuFwd M m kW := by
    unfold nuFwd; positivity
  intro f1 f2 pf
  rw [hEqv]
  set D := 2 * dd M m kW
  set h := HH1 M m kW
  set ω := omegaFwd M m kW
  have hD : 0 < D := by positivity
  have hdiff : D - h ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hnu; linarith
  constructor
  · rintro ⟨hpf, e1, e2⟩
    rw [eq_div_iff hD.ne'] at e1 e2
    have hf : f1 = f2 := by
      have : (f1 - f2) * (D + h) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · linarith
    have hf1 : f1 = ω / nuFwd M m kW := by
      rw [hnu, eq_div_iff (by positivity)]
      rw [← hf] at e1
      linarith
    refine ⟨hf1, hf ▸ hf1, ?_⟩
    rw [hpf, ← hf, hf1]
    simp only [hPF]
    ring
  · rintro ⟨e1, e2, e3⟩
    simp only [fStar] at e1 e2
    have hf : f1 = f2 := by rw [e1, e2]
    refine ⟨?_, ?_, ?_⟩
    · rw [e3, ← hf, e1]; simp only [hPF]; ring
    · rw [eq_div_iff hD.ne', ← hf, e1, hnu]
      field_simp
      ring
    · rw [eq_div_iff hD.ne', hf, e2, hnu]
      field_simp
      ring

end RFT1

theorem solution (M : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ) (kW : ℝ) (hkW : 0 ≤ kW) :
    (∀ f1 f2 pf : ℝ, IsFwdEq M P θ ξ kW f1 f2 pf ↔
      f1 = fStar M (momentsOf P θ ξ) kW ∧ f2 = fStar M (momentsOf P θ ξ) kW ∧
        pf = aF M (momentsOf P θ ξ) kW
          - 2 * bF M (momentsOf P θ ξ) kW * omegaFwd M (momentsOf P θ ξ) kW
            / nuFwd M (momentsOf P θ ξ) kW) ∧
    (∀ w : Ω,
      spotQ M θ ξ kW (fStar M (momentsOf P θ ξ) kW) (fStar M (momentsOf P θ ξ) kW) w
          = q0 M θ ξ kW w / 3
            + omegaFwd M (momentsOf P θ ξ) kW / (3 * nuFwd M (momentsOf P θ ξ) kW) ∧
      spotP M θ ξ kW (fStar M (momentsOf P θ ξ) kW + fStar M (momentsOf P θ ξ) kW) w
          = p0 M θ ξ kW w / 3
            - 2 * omegaFwd M (momentsOf P θ ξ) kW / (3 * nuFwd M (momentsOf P θ ξ) kW)) := by
  refine ⟨RFT1.main M P θ ξ hS kW, fun w => ⟨?_, ?_⟩⟩
  · simp only [spotQ, fStar]; ring
  · simp only [spotP, fStar]; ring
