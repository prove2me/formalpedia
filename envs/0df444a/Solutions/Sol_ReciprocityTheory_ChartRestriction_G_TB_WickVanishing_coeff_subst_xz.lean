-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:45.032787+00:00
-- url     : https://prove2.me/submissions/a279e13b-36a5-4bd5-871e-f6d1fda24cbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_one_le_iInf_order
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_first_axis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_second_axis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {τ : Type*} (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (a : Fin 2 × Fin d → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (n : τ →₀ ℕ) (hn : n.degree = 2) :
    coeff n (subst a h) = ∑ l, ∑ m, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1) h *
      coeff n (a (0, l) * a (1, m)) := by
  classical
  nontriviality k
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let g : Fin d × Fin d → (Fin 2 × Fin d →₀ ℕ) := fun p => single ((0 : Fin 2), p.1) 1 + single ((1 : Fin 2), p.2) 1
  have hg : Function.Injective g := by
    rintro ⟨l, m⟩ ⟨l', m'⟩ e
    have e0 := congrArg (· ((0 : Fin 2), l)) e
    have e1 := congrArg (· ((1 : Fin 2), m)) e
    simp only [g, Finsupp.add_apply, single_apply, Prod.mk.injEq] at e0 e1
    simp only [true_and] at e0 e1
    have n01 : ((1 : Fin 2) = 0) = False := by simp
    have n10 : ((0 : Fin 2) = 1) = False := by simp
    simp only [n01, n10, false_and, and_false, if_false, add_zero, zero_add] at e0 e1
    split_ifs at e0 e1 <;> simp_all
  have hprod : ∀ D : Fin 2 × Fin d →₀ ℕ, D.prod (fun s e => a s ^ e) = subst a (monomial D (1 : k)) := fun D => by
    rw [subst_monomial hs, map_one, one_mul]
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.image g Finset.univ) ?_,
    Finset.sum_image (fun p _ q _ e => hg e), ← Finset.univ_product_univ, Finset.sum_product]
  · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    have hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m) := fun e => absurd (congrArg Prod.fst e) (by simp)
    rw [smul_eq_mul]
    congr 2
    show (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1).prod (fun s e => a s ^ e) = _
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp [Finsupp.prod_single_index]
  · intro D hD
    rw [Function.mem_support] at hD
    have hc : coeff D h ≠ 0 := fun e => hD (by rw [e, zero_smul])
    have hp : coeff n (D.prod fun s e => a s ^ e) ≠ 0 := fun e => hD (by rw [e, smul_zero])
    have hx : ∃ l, D (0, l) ≠ 0 := by
      by_contra hx; push Not at hx; exact hc (coeff_eq_zero_of_vanish_first_axis h h0 D hx)
    have hz : ∃ m, D (1, m) ≠ 0 := by
      by_contra hz; push Not at hz; exact hc (coeff_eq_zero_of_vanish_second_axis h h1 D hz)
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hz
    have hdeg : D.degree ≤ 2 := by
      by_contra hlt
      push Not at hlt
      apply hp
      rw [hprod]
      apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (le_order_subst hs _)
      rw [order_monomial_of_ne_zero one_ne_zero, hn]
      calc ((2 : ℕ) : ℕ∞) < (D.degree : ℕ∞) := by exact_mod_cast hlt
        _ = 1 * (D.degree : ℕ∞) := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (one_le_iInf_order a ha) le_rfl
    rw [eq_xz hl hm hdeg]
    exact Finset.mem_image.2 ⟨(l, m), Finset.mem_univ _, rfl⟩
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
