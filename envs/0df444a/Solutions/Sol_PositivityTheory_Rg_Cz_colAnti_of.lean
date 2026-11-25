-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.colAnti_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:06.416649+00:00
-- url     : https://prove2.me/submissions/962d4151-df12-42ae-9382-9422b58b7869

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_swap_iff
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_adj
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_lt
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_pm_single
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_colD
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_eq_of_le
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_npairs_le
import Theorems.Thm_PositivityTheory_Rg_Cz_alt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_cA_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open ColumnAntisymmetry
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → Height → ColAnti := by
  intro _ hJM hH n M _ _ E hE ℓ hWh top htop m col b hmono hb
  obtain ⟨hc, hP, _⟩ := hJM n M E hE m
  obtain ⟨hH1, _, _⟩ := hH n M E hE ℓ hWh top htop
  have hdeg := hH1 (Fin m) (npairs col) (colD E col) (deg_colD E col)
  set L : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col with hL
  have hLs : ∀ I v, L (Pi.single I v) = ℓ (colD E col (Pi.single I v) fun _ => top) := fun _ _ => rfl
  have hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q) := by
    have hadj := fun i j hij hcol => Q_adj E ℓ top col hmono hc hP i j hij hcol
    intro p q hpq hcol
    rcases lt_or_gt_of_ne hpq with h | h
    · exact Q_lt L col hmono hadj ((q : ℕ) - p - 1) p q (by omega) hcol
    · rw [Equiv.swap_comm]
      exact Q_lt L col hmono hadj ((p : ℕ) - q - 1) q p (by omega) hcol.symm
  have hQ := Q_colG L col hsw
  have hbinj : ColInj col b := hb.1
  obtain ⟨c, hcb⟩ : ∃ c : ℂ, ∀ v, L (Pi.single b v) = c * ℓ v := by
    rcases (npairs_le col top htop b hbinj).lt_or_eq with hlt | heq
    · exact ⟨0, fun v => by rw [hLs, (hdeg b).1 hlt v]; simp⟩
    · obtain ⟨c, hc⟩ := (hdeg b).2 heq
      exact ⟨c, fun v => by rw [hLs, hc v]⟩
  have hmemG : ∀ σ ∈ colG col, ∀ p, col (σ p) = col p := fun σ hσ => by simpa [colG] using hσ
  have hval : ∀ σ ∈ colG col, ∀ v, L (Pi.single (b ∘ σ) v) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * (c * ℓ v) := by
    intro σ hσ v
    have hσ' : σ⁻¹ ∈ colG col := by
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      have := hmemG σ hσ (σ⁻¹ p)
      simp at this
      exact this.symm
    have e : (Pi.single (b ∘ σ) v : TV n M (Fin m)) = pm σ⁻¹ (Pi.single b v) := by
      rw [pm_single, inv_inv]
    rw [e, ← LinearMap.comp_apply, hQ _ hσ', LinearMap.smul_apply, hcb, Equiv.Perm.sign_inv, smul_eq_mul]
  have hzero : ∀ I : Fin m → Fin n, I ∉ (colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ) → ∀ v, L (Pi.single I v) = 0 := by
    intro I hI v
    by_cases hinj : ColInj col I
    · have hle := npairs_le col top htop I hinj
      rcases hle.lt_or_eq with hlt | heq
      · rw [hLs, (hdeg I).1 hlt v]
      · exfalso
        obtain ⟨σ, hσ, e⟩ := eq_of_le col top htop b I hb hinj heq.ge
        exact hI (Finset.mem_image.mpr ⟨σ, hσ, e.symm⟩)
    · simp only [ColInj, not_forall] at hinj
      obtain ⟨p, q, hcol, hIpq, hpq⟩ := hinj
      have hfix : (Pi.single I v : TV n M (Fin m)) = pm (Equiv.swap p q) (Pi.single I v) := by
        rw [pm_single, Equiv.swap_inv]
        congr 1
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · rw [h1, hIpq]
        · rw [h2, hIpq]
        · rfl
      have h := (Q_swap_iff L hpq).mp (hsw p q hpq hcol)
      have h2 : L (Pi.single I v) = -L (Pi.single I v) := by
        conv_lhs => rw [hfix]
        rw [← LinearMap.comp_apply, h, LinearMap.neg_apply]
      have h3 : (2 : ℂ) * L (Pi.single I v) = 0 := by linear_combination h2
      simpa using h3
  refine ⟨c, LinearMap.ext fun f => ?_⟩
  show L f = c * ℓ (cA col b f)
  rw [cA_apply, alt_apply, map_sum]
  conv_lhs => rw [← Finset.univ_sum_single f, map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ ((colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ)))
    (fun I _ hI => hzero I hI (f I))]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [hval σ hσ, map_smul, smul_eq_mul]
    ring
  · intro σ hσ τ hτ e
    refine Equiv.ext fun p => hb.1 _ _ ?_ (congrFun e p)
    rw [hmemG σ hσ, hmemG τ hτ]
end PositivityTheory.Rg.Cz
