-- Prove2me | solution 1 for P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:06:57.241125+00:00
-- url     : https://prove2.me/submissions/fab294b3-1589-4fe5-98b1-e991f39d2bed

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_cFactor_ne_zero
import Theorems.Thm_ChromaticReconstruction_pderiv_phi_uniform
import Theorems.Thm_ChromaticReconstruction_card_eq_of_chromSymm_eq
import Theorems.Thm_ChromaticReconstruction_card_eq_of_phi_eq
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm_replicate_one
import Theorems.Thm_ChromaticReconstruction_coeff_pderiv_sub
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pderiv_chromSymm_eq_zero
import Theorems.Thm_ChromaticReconstruction_phi_uniformLeafExt_eq_opD
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q)
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Connected) (hH : H.Connected) :
    phi (uniformLeafExt q G) = phi (uniformLeafExt q H) ↔ chromSymm G = chromSymm H := by
  set N := Fintype.card V + Fintype.card W + 3
  constructor
  · intro h
    have ht := card_eq_of_phi_eq hq hG hH h
    -- equality of all derivatives `∂/∂p_r` for `r ≥ 2`
    have hder : ∀ r, r ≠ 1 → pderiv r (chromSymm G) = pderiv r (chromSymm H) := by
      intro r hr1
      rcases Nat.lt_or_ge r 2 with hr | hr
      · have : r = 0 := by omega
        rw [pderiv_chromSymm_eq_zero G r (Or.inl this),
          pderiv_chromSymm_eq_zero H r (Or.inl this)]
      rcases Nat.lt_or_ge r N with hrN | hrN
      · have e := congrArg (pderiv (q * r - 1)) h
        have hqr : q * r - 1 ≠ 1 := by
          have : q * 2 ≤ q * r := Nat.mul_le_mul_left q hr
          omega
        rw [pderiv_phi_uniform q N r hq G (by omega) hrN (by omega) hqr,
          pderiv_phi_uniform q N r hq H (by omega) hrN (by omega) hqr, ht] at e
        have e' := smul_right_injective _ (cFactor_ne_zero hq (Fintype.card W)) e
        have hC : (C (r : ℚ) : MvPolynomial ℕ ℚ) ≠ 0 := by
          rw [Ne, C_eq_zero]; exact_mod_cast (by omega : r ≠ 0)
        have e'' := mul_left_cancel₀ hC e'
        exact rename_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left (by omega) hab) e''
      · rw [pderiv_chromSymm_eq_zero G r (Or.inr (by omega)),
          pderiv_chromSymm_eq_zero H r (Or.inr (by omega))]
    ext d
    by_contra hd
    have hsupp : ∀ r, r ≠ 1 → d r = 0 := by
      intro r hr1
      by_contra hdr
      have e := congrArg (coeff (d - Finsupp.single r 1)) (hder r hr1)
      rw [coeff_pderiv_sub _ _ _ (by omega), coeff_pderiv_sub _ _ _ (by omega)] at e
      exact hd (mul_left_cancel₀ (by exact_mod_cast hdr) e)
    have hdeq : d = Multiset.toFinsupp (Multiset.replicate (d 1) 1) := by
      ext x
      rw [Multiset.toFinsupp_apply, Multiset.count_replicate]
      by_cases hx : x = 1
      · subst hx; simp
      · rw [hsupp x hx]; simp [Ne.symm hx]
    apply hd
    rw [hdeq, coeff_chromSymm_replicate_one, coeff_chromSymm_replicate_one, ht]
  · intro h
    have ht := card_eq_of_chromSymm_eq h
    rw [phi_uniformLeafExt_eq_opD q N hq G (by omega), phi_uniformLeafExt_eq_opD q N hq H (by omega),
      h, ht]
end ChromaticReconstruction
