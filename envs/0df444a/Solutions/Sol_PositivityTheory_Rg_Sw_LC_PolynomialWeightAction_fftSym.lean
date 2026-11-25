-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.fftSym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:41.568581+00:00
-- url     : https://prove2.me/submissions/8eb88c75-9d9e-462b-90d5-397d7721c631

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_phi_injective
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_vars_subset
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_rename_vec
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_rename_cov
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_eq_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_transvection
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_unitary

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution : FFTSym := by
  intro hFFT m n ε s hs hK
  obtain ⟨p, rfl⟩ := exists_rename_eq_of_vars_subset_range s (phi ε) (phi_injective ε) (vars_subset ε s hs)
  have hD : ∀ i j, Dsrc (m := m) i j p = 0 := fun i j => Dsrc_eq_zero ε i j p (hK i j)
  have hinv : ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit g → act g p = p := by
    intro g hg
    refine Matrix.diagonal_transvection_induction (fun M => IsUnit M → act M p = p) g ?_ ?_ ?_ hg
    · intro D _ hU
      apply act_diag D _ p (fun l => hD l l)
      intro l hl
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal] at hU
      exact (Finset.prod_ne_zero_iff.mp hU.ne_zero) l (Finset.mem_univ l) hl
    · intro t _
      exact act_transvection t p (hD t.j t.i)
    · intro A B hA hB hAB
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, IsUnit.mul_iff] at hAB
      rw [act_mul, hA ((Matrix.isUnit_iff_isUnit_det A).mpr hAB.1),
        hB ((Matrix.isUnit_iff_isUnit_det B).mpr hAB.2)]
  have hu := hFFT (Fin n) (Fin m) (Fin m) p (fun u hu => by
    rw [← act_unitary u hu]
    exact hinv u ((Matrix.isUnit_iff_isUnit_det u).mpr
      (isUnit_iff_exists_inv.mpr ⟨(star u).det, by
        rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hu, Matrix.det_one]⟩)))
  have h2 : rename (phi ε) p ∈ (Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m =>
      ∑ i, (X (Sum.inl (i, ab.1)) : MvPolynomial (FinalTheorems m n) ℂ) * X (Sum.inr (i, ab.2)))).map (rename (phi ε)) :=
    Subalgebra.mem_map.mpr ⟨p, hu, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h2
  convert h2 using 3
  funext ab
  simp only [Function.comp_apply, map_sum, map_mul, rename_vec, rename_cov, pairSym]
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
