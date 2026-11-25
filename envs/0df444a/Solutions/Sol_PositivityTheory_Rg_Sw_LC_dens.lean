-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:01.064341+00:00
-- url     : https://prove2.me/submissions/d8d878a1-6a14-4ceb-9940-a369de0f52ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_f_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_f_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_f_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_renameL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_renameL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.B1
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : Dens := by
  intro m n ε R T hT
  classical
  let M : ℕ := R.sup (fun r => Finset.univ.sup r)
  let bnd : (Fin m × Fin n × Bool) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => M)
  let Γ := (Finset.Iic bnd).filter (fun δ => (∀ k ∈ δ.support, inF1 ε k) ∧ rdeg ε δ ∈ R)
  have hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k := fun γ hγ => (Finset.mem_filter.mp hγ).2.1
  have memΓ : ∀ δ : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k ∈ δ.support, inF1 ε k) → rdeg ε δ ∈ R → δ ∈ Γ := by
    intro δ h1 h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr fun k => ?_, h1, h2⟩
    show δ k ≤ M
    by_cases hk : δ k = 0
    · omega
    · have hF := h1 k (Finsupp.mem_support_iff.mpr hk)
      have hkeq : k = (k.1, k.2.1, !ε k.1) := by
        obtain ⟨a, i, b⟩ := k; simp only [inF1] at hF; simp [hF]
      have h3 : δ k ≤ rdeg ε δ k.1 := by
        unfold rdeg
        conv_lhs => rw [hkeq]
        exact Finset.single_le_sum (f := fun i => δ (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k.2.1)
      have h4 : rdeg ε δ k.1 ≤ Finset.univ.sup (rdeg ε δ) := Finset.le_sup (f := rdeg ε δ) (Finset.mem_univ _)
      have h5 : Finset.univ.sup (rdeg ε δ) ≤ M := Finset.le_sup (f := fun r => Finset.univ.sup r) h2
      omega
  have mono_mem : ∀ γ ∈ Γ, (monomial γ 1 : PX m n) ∈ box ε (R : Set (Fin m → ℕ)) := fun γ hγ =>
    Submodule.subset_span ⟨γ, hΓ γ hγ, (Finset.mem_filter.mp hγ).2.2, rfl⟩
  have hind := indicator ε Γ hΓ Γ.card
  choose! P hP using fun γ (hγ : γ ∈ Γ) => hind γ hγ (Finset.card_filter_le _ _)
  refine ⟨∑ γ ∈ Γ, rename Sum.inl (T (monomial γ 1)) * P γ,
    sf_sum ε _ _ fun γ hγ => sf_renameL ε _ (hT _ (mono_mem γ hγ)) (hP γ hγ).1, ?_⟩
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, h1, h2, rfl⟩ := hx
    have hδ := memΓ δ h1 h2
    rw [op_sum]
    simp only [op_renameL]
    rw [Finset.sum_congr rfl fun γ hγ => by rw [(hP γ hγ).2 δ hδ]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hδ]
  | zero => rw [op_f_zero, map_zero]
  | add x y _ _ hx hy => rw [op_f_add, map_add, hx, hy]
  | smul a x _ hx => rw [op_f_smul, map_smul, hx]
end PositivityTheory.Rg.Sw.LC
