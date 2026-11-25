-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.maj_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:21.906133+00:00
-- url     : https://prove2.me/submissions/b6c92816-5b70-49af-a5e3-b68c9f48fda3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_plane_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz
private theorem hermC_Gm_add_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u + u') v = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem hermC_Gm_sub_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u - u') v = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem hermC_Gm_smul_left (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (c • u) v = c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
private theorem hermC_Gm_add_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v + v') = hermC τ.1 X.Gm u v + hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
private theorem hermC_Gm_sub_right (u v v' : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v - v') = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
private theorem hermC_Gm_smul_right (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u (c • v) = conj c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
private theorem hermC_Gm_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, f a) v = ∑ a, hermC τ.1 X.Gm (f a) v :=
  map_sum (AddMonoidHom.mk' (fun u => hermC τ.1 X.Gm u v)
    (fun u u' => hermC_Gm_add_left X τ hz u u' v)) f Finset.univ
private theorem det_gramPos_ne_zero : (X.gramPos z τ).det ≠ 0 := by
  have hz' : ∀ ψ : X.Ψ, (mat z ψ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm z ψ i).re := hz
  have h2 := (hz' τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  have hd : dmin X.Gm z τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos z τ).det := rfl
  intro h0
  rw [hd, h0] at h2
  simp at h2
private theorem hermC_ppos_col_castLE (u : Fin r → ℂ) (k : Fin X.p0) :
    hermC τ.1 X.Gm (X.ppos z τ u) (col (mat z τ) (Fin.castLE X.p0_le k)) =
      hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le k)) := by
  have hinv : (X.gramPos z τ)⁻¹ * X.gramPos z τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_gramPos_ne_zero X τ hz))
  have hgk : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a))
      (col (mat z τ) (Fin.castLE X.p0_le b)) = X.gramPos z τ a b := fun a b => rfl
  rw [Data.ppos, hermC_Gm_sum_left X τ hz]
  simp only [hermC_Gm_smul_left X τ hz, hgk]
  calc ∑ a, (∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          (X.gramPos z τ)⁻¹ b a) * X.gramPos z τ a k
      = ∑ b, hermC τ.1 X.Gm u (col (mat z τ) (Fin.castLE X.p0_le b)) *
          ((X.gramPos z τ)⁻¹ * X.gramPos z τ) b k := by
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = _ := by
        rw [hinv]
        simp [Matrix.one_apply]
private theorem hermC_ppos_right_eq_sum_gramPos_inv (x w : Fin r → ℂ) :
    hermC τ.1 X.Gm x (X.ppos z τ w) = ∑ a, conj (∑ b, hermC τ.1 X.Gm w
      (col (mat z τ) (Fin.castLE X.p0_le b)) * (X.gramPos z τ)⁻¹ b a) *
        hermC τ.1 X.Gm x (col (mat z τ) (Fin.castLE X.p0_le a)) := by
  rw [← FD.hermC_conj τ.1 X.Gm_herm (X.ppos z τ w) x, Data.ppos, hermC_Gm_sum_left X τ hz, map_sum]
  simp only [hermC_Gm_smul_left X τ hz, map_mul, FD.hermC_conj τ.1 X.Gm_herm]
private theorem hermC_ppos_ppos (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) (X.ppos z τ w) = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [hermC_ppos_right_eq_sum_gramPos_inv X τ hz (X.ppos z τ u) w, hermC_ppos_right_eq_sum_gramPos_inv X τ hz u w]
  simp only [hermC_ppos_col_castLE X τ hz]
private theorem hermC_ppos_self_adjoint (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos z τ u) w = hermC τ.1 X.Gm u (X.ppos z τ w) := by
  rw [← FD.hermC_conj τ.1 X.Gm_herm w (X.ppos z τ u), ← hermC_ppos_ppos X τ hz w u,
    FD.hermC_conj τ.1 X.Gm_herm, hermC_ppos_ppos X τ hz u w]
private theorem hermC_jp_left_eq_hermC_jp_right (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) w = hermC τ.1 X.Gm u (X.jp z τ w) := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat, hermC_ppos_self_adjoint X τ hz]
private theorem hermC_jp_jp' (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp z τ u) (X.jp z τ w) = hermC τ.1 X.Gm u w := by
  simp only [Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_sub_right X τ hz,
    hermC_Gm_smul_right X τ hz, map_ofNat]
  rw [hermC_ppos_ppos X τ hz u w, hermC_ppos_self_adjoint X τ hz u w]
  ring
private theorem ppos_add' (u w : Fin r → ℂ) :
    X.ppos z τ (u + w) = X.ppos z τ u + X.ppos z τ w := by
  simp only [Data.ppos, hermC_Gm_add_left X τ hz, add_mul, Finset.sum_add_distrib, add_smul]
private theorem ppos_smul_eq_smul_ppos (t : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (t • u) = t • X.ppos z τ u := by
  simp only [Data.ppos, hermC_Gm_smul_left X τ hz, Finset.smul_sum, smul_smul, Finset.mul_sum,
    mul_assoc]
private theorem jp_add' (u w : Fin r → ℂ) :
    X.jp z τ (u + w) = X.jp z τ u + X.jp z τ w := by
  simp only [Data.jp, ppos_add' X τ hz, smul_add]
  abel
private theorem jp_smul' (t : ℂ) (u : Fin r → ℂ) :
    X.jp z τ (t • u) = t • X.jp z τ u := by
  simp only [Data.jp, ppos_smul_eq_smul_ppos X τ hz, smul_sub, smul_smul]
  rw [mul_comm]
private theorem maj_eq_re_hermC_jp (v : Fin r → ℂ) :
    X.maj z τ v = (hermC τ.1 X.Gm (X.jp z τ v) v).re := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ v) v = ∑ a, ∑ b,
      hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    rw [Data.ppos, hermC_Gm_sum_left X τ hz]
    simp only [hermC_Gm_smul_left X τ hz, FD.hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [Data.maj, Data.posPart, Data.jp, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, ← h1]
  simp [Complex.sub_re, Complex.mul_re]
private theorem maj_add_smul (v u : Fin r → ℂ) (t : ℂ) :
    X.maj z τ (v + t • u) = X.maj z τ v +
      2 * (conj t * hermC τ.1 X.Gm (X.jp z τ v) u).re + Complex.normSq t * X.maj z τ u := by
  have hs : hermC τ.1 X.Gm (X.jp z τ u) v = conj (hermC τ.1 X.Gm (X.jp z τ v) u) := by
    rw [FD.hermC_conj τ.1 X.Gm_herm, hermC_jp_left_eq_hermC_jp_right X τ hz]
  rw [maj_eq_re_hermC_jp X τ hz (v + t • u), maj_eq_re_hermC_jp X τ hz v, maj_eq_re_hermC_jp X τ hz u,
    jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
    hermC_Gm_add_right X τ hz, hermC_Gm_add_right X τ hz, hermC_Gm_smul_right X τ hz, hermC_Gm_smul_right X τ hz, hs]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring
end BoostLowerBounds
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz
namespace ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
theorem _root_.solution (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) (w0 : Fin r → ℂ)
    (h0e : hermC τ.1 X.Gm w0 e = 0) (h0f : hermC τ.1 X.Gm w0 (X.jp z τ e) = 0) (a b : ℂ) :
    X.maj z τ (w0 + a • e + b • X.jp z τ e) =
      X.maj z τ w0 + (Complex.normSq a + Complex.normSq b) * X.maj z τ e := by
  obtain ⟨-, hff, -, -⟩ := plane_facts X τ hz hee he0
  have hjw : hermC τ.1 X.Gm (X.jp z τ w0) e = 0 := by
    rw [hermC_jp_left_eq_hermC_jp_right X τ hz, h0f]
  have hjf : hermC τ.1 X.Gm (X.jp z τ (w0 + a • e)) (X.jp z τ e) = 0 := by
    rw [jp_add' X τ hz, jp_smul' X τ hz, hermC_Gm_add_left X τ hz, hermC_Gm_smul_left X τ hz,
      hermC_jp_jp' X τ hz w0 e, h0e, hff, mul_zero, add_zero]
  have hmf : X.maj z τ (X.jp z τ e) = X.maj z τ e := by
    rw [maj_eq_re_hermC_jp X τ hz (X.jp z τ e), maj_eq_re_hermC_jp X τ hz e, hermC_jp_jp' X τ hz (X.jp z τ e) e]
  rw [maj_add_smul X τ hz (w0 + a • e), maj_add_smul X τ hz w0, hjw, hjf, hmf]
  simp only [mul_zero, Complex.zero_re, add_zero]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
