-- Prove2me | solution 1 for PI.WeylForKWork.typePl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:52.849183+00:00
-- url     : https://prove2.me/submissions/79789e22-3a2e-45a6-94f2-0d20438b531d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TypePlOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix PI.WeylForKInhab
private theorem diagonal_exp_mem_Kset {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  · show diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Jm ε = Jm ε * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
private theorem isWtOn_sPl (hD : BlockDiag) {N : ℕ} (ε : Fin N → Bool) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ν : Fin N → ℝ) (u : H)
    (hu : IsWtOn (Kset ε) σ ν u) : IsWtOn (Kset (allPos (nPl ε))) (sPl ε σ) (fun i => ν (ePl ε i)) u := by
  intro θ _
  obtain ⟨θ', h1, h2, h3⟩ := (hD N ε).2.1 θ
  show σ (iPl ε (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)))) u = _
  rw [h3, hu θ' (diagonal_exp_mem_Kset ε θ'),
    show (∑ a, ν a * θ' a) = ∑ i, ν (ePl ε i) * θ' (ePl ε i) + ∑ j, ν (eMi ε j) * θ' (eMi ε j) from
      (hD N ε).1 (fun a => ν a * θ' a)]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
end PI.WeylForKWork
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix PI.WeylForKInhab
namespace PI.WeylForKWork
theorem _root_.solution (hB : Blocks) (hD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) : TypePl := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  have hσP := (hB5 H σ hσ).1
  haveI : FiniteDimensional ℂ S := hS.1
  obtain ⟨v, hvS, hv0, hvw⟩ := hS.2.2.2.1
  have hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S := fun h hh u hu => hS.2.1 _ (hB1 h hh) u hu
  obtain ⟨X, hXS, hXst, hXirr, x, hxX, hx0, hxw⟩ := hM (nPl ε) H (sPl ε σ) S
    (fun i => Λ (ePl ε i)) v hσP hS.1 hstP hvS hv0 (isWtOn_sPl hD ε σ Λ v hvw)
  refine ⟨X, hXS, Submodule.finiteDimensional_of_le hXS, hXst, hXirr, ⟨x, hxX, hx0, hxw⟩, ?_⟩
  intro μ w hwX hw0 hww
  let Wμ : Submodule ℂ H :=
    { carrier := {u | u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) →
          sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u}
      add_mem' := fun hx hy => ⟨S.add_mem hx.1 hy.1, fun θ hθ => by
        rw [map_add, hx.2 θ hθ, hy.2 θ hθ, smul_add]⟩
      zero_mem' := ⟨S.zero_mem, fun θ _ => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun θ hθ => by
        rw [map_smul, hx.2 θ hθ, smul_comm]⟩ }
  have hmem : ∀ u, u ∈ Wμ ↔ (u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) →
      sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u) :=
    fun u => Iff.rfl
  have hWst : ∀ θ : Fin N → ℝ, ∀ u ∈ Wμ, σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u ∈ Wμ := by
    intro θ u hu
    rw [hmem] at hu ⊢
    refine ⟨hS.2.1 _ (diagonal_exp_mem_Kset ε θ) u hu.1, fun φ hφ => ?_⟩
    obtain ⟨φ', -, -, hφ'⟩ := (hD N ε).2.1 φ
    have hcomm : iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) := by
      rw [hφ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact mul_comm _ _
    have hm1 := hσ.1.2 _ (hB1 _ hφ) _ (diagonal_exp_mem_Kset ε θ)
    have hm2 := hσ.1.2 _ (diagonal_exp_mem_Kset ε θ) _ (hB1 _ hφ)
    have hu2 : σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) u = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • u :=
      hu.2 φ hφ
    show σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) (σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u) =
      Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u
    rw [← ContinuousLinearMap.comp_apply, ← hm1, hcomm, hm2, ContinuousLinearMap.comp_apply, hu2, map_smul]
  have hwW : w ∈ Wμ := (hmem w).2 ⟨hXS hwX, hww⟩
  have hW0 : Wμ ≠ ⊥ := by
    intro h
    rw [h] at hwW
    exact hw0 ((Submodule.mem_bot ℂ).1 hwW)
  have hWS : Wμ ≤ S := fun u hu => ((hmem u).1 hu).1
  haveI : FiniteDimensional ℂ Wμ := Submodule.finiteDimensional_of_le hWS
  obtain ⟨ν, u, huW, hu0, huw⟩ := hT N ε H σ Wμ hσ inferInstance hW0 hWst
  have hCD := hS.2.2.2.2 ν u (hWS huW) hu0 huw
  have hres := (hC N ε ν Λ hCD).1
  have hμν : μ = fun i => ν (ePl ε i) :=
    hW (nPl ε) H (sPl ε σ) μ _ u hu0 ((hmem u).1 huW).2 (isWtOn_sPl hD ε σ ν u huw)
  rw [hμν]
  exact hres
end PI.WeylForKWork
