-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.nsmul_coprime_bijective_curves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:34.645131+00:00
-- url     : https://prove2.me/submissions/e91db5ba-05ec-48d2-a8a3-267ae09497fb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_nsmulF_eq_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_isCurve_iff_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_solve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_subst_lin_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem valuation_natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) (n : ℕ)
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have hcop : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨u, w, huw⟩ := hcop
  have hC : (u : C) * p + (w : C) * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) huw
  have hu : 0 ≤ v (u : C) := intCast_mem (ptIntSub v) u
  have hw : 0 ≤ v (w : C) := intCast_mem (ptIntSub v) w
  have hn0 : 0 ≤ v (n : C) := natCast_mem (ptIntSub v) n
  refine le_antisymm ?_ hn0
  by_contra hpos
  push_neg at hpos
  have h1 : 0 < v ((u : C) * p) := by
    rw [v.map_mul, hvp]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hu)
  have h2 : 0 < v ((w : C) * n) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_left hw)
  have h3 := v.map_add ((u : C) * p) ((w : C) * n)
  rw [hC, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))
private theorem exists_eq_single_of_degree_eq_one {σ : Type} (α : σ →₀ ℕ) (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨s, ?_⟩
  have hsum : ∑ i ∈ α.support, α i = 1 := by rw [← h]; rfl
  have hle : α s ≤ 1 := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  have hs1 : α s = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
  have hrest : ∑ i ∈ α.support.erase s, α i = 0 := by
    rw [← Finset.add_sum_erase _ _ hs, hs1] at hsum
    omega
  ext i
  by_cases hi : i = s
  · subst hi
    simp [hs1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne'
    have hmem : i ∈ α.support.erase s :=
      Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hne'⟩
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    omega
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1)
    (n : ℕ) (hn : ¬ p ∣ n) (gb : Fin d → PowerSeries C) (hgb : IsCurve v gb) :
    ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb := by
  have hn0' : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have hn0 : (n : C) ≠ 0 := by exact_mod_cast hn0'
  have hvn := valuation_natCast_eq_zero_of_not_dvd hp hvp n hn
  have hvinv : (n : C)⁻¹ ∈ ptIntSub v := by
    show 0 ≤ v (n : C)⁻¹
    have h := v.map_mul (n : C) (n : C)⁻¹
    rw [mul_inv_cancel₀ hn0, v.map_one, hvn, zero_add] at h
    rw [← h]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) C, M = (n : C) • 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin d) (Fin d) C, N = (n : C)⁻¹ • 1 := ⟨_, rfl⟩
  have hNM : N * M = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hn0, one_smul]
  have hMN : M * N = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hn0, one_smul]
  have hMab : ∀ a b, M a b = if a = b then (n : C) else 0 := by
    intro a b
    rw [hM, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i j, N i j ∈ ptIntSub v := by
    intro i j
    rw [hN, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact hvinv
    · rw [mul_zero]; exact (ptIntSub v).zero_mem
  have hMint : ∀ a b, M a b ∈ ptIntSub v := by
    intro a b
    rw [hMab]
    split_ifs
    · exact natCast_mem (ptIntSub v) n
    · exact (ptIntSub v).zero_mem
  obtain ⟨K, hK⟩ : ∃ K : Fin d → MvPowerSeries (Fin d) C,
      K = fun b => ptNs G n b - ∑ a, M a b • X a := ⟨_, rfl⟩
  have hK0 : ∀ b, constantCoeff (K b) = 0 := by
    intro b
    simp [hK, ptNs_const]
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := by
    intro b
    rw [hK]
    exact (ptIntSer v (Fin d)).sub_mem (ptNs_int G n b)
      ((ptIntSer v (Fin d)).sum_mem fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hKdeg : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α hα
    left
    by_contra hlt
    push_neg at hlt
    apply hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with hd | hd
    · rw [(Finsupp.degree_eq_zero_iff α).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        hK0 b]
    · obtain ⟨s, rfl⟩ := exists_eq_single_of_degree_eq_one α hd
      rw [hK]
      simp only [map_sub, map_sum, MvPowerSeries.coeff_smul, ptNs_lin, MvPowerSeries.coeff_X,
        Finsupp.single_left_inj one_ne_zero, hMab, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hf : PTGood v gb := isCurve_iff_good.mp hgb
  have key : ∀ y : Fin d → PowerSeries C, PTGood v y →
      (G.nsmulF n y = gb ↔ ∀ b, ∑ a, M a b • y a + subst y (K b) = gb b) := by
    intro y hy
    have hys : HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => (hy a).1
    rw [nsmulF_eq_subst G hys n]
    constructor
    · intro h b
      rw [← congrFun h b, pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), hK]
    · intro h
      funext b
      rw [pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), ← h b, hK]
  obtain ⟨x, ⟨hx, hxeq⟩, huniq⟩ := pt_solve (A := fun x => x) (K := K) (M := M) (N := N) (f := gb)
    hNM hMN hNint hf (fun x hx s => (hx s).1) (fun x hx s => (hx s).2)
    (fun k x y _ _ hxy s e he => hxy s e he) hKdeg hKi hK0
  refine ⟨x, ⟨isCurve_iff_good.mpr hx, (key x hx).mpr hxeq⟩, fun y hy => ?_⟩
  have hyg := isCurve_iff_good.mp hy.1
  exact huniq y ⟨hyg, (key y hyg).mp hy.2⟩
end ReciprocityTheory.ChartRestriction.G.Sh
