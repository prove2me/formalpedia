-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:03.725013+00:00
-- url     : https://prove2.me/submissions/7ff252d1-be46-4e2e-8c51-253324c13c1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lg_agree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_pcurve_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lgCurve_sub_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_pcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isIntV_vecMul_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem exists_subring_mem_iff_isIntV : ∃ S : Subring C, ∀ x, x ∈ S ↔ IsIntV v x :=
  ⟨{ carrier := {x | 0 ≤ v x}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
       exact add_nonneg ha hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }, fun _ => Iff.rfl⟩
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hgaC : IsCurve v ga) (hga : G.IsPTypical p ga) :
    ∀ n b, IsIntV v (ptx G p γ ga n b) := by
  obtain ⟨S, hS⟩ := exists_subring_mem_iff_isIntV (v := v)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b
    have hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b) := fun s hs b => ih s hs b
    have hagree := lg_agree G hp hγ hγt hdet ga hga n hx
    have hα : ∀ c, PowerSeries.constantCoeff (ga c) = 0 := fun c => (hgaC c).1
    have hpcC := isCurve_pcurve G hp.ne_zero hγ (ptx G p γ ga) n hx
    have hβ : ∀ c, PowerSeries.constantCoeff (pcurve G p γ (ptx G p γ ga) n c) = 0 :=
      fun c => (hpcC c).1
    have hw : ∀ c, IsIntV v (ptw G p γ ga n c) := by
      intro c
      have h1 := coeff_lgCurve_sub_eq G hα hβ (p ^ n) hagree c
      have h2 := coeff_lg_pcurve_top G hp hγ (ptx G p γ ga) n hx c
      have e : ptw G p γ ga n c =
          PowerSeries.coeff (p ^ n) (ga c - pcurve G p γ (ptx G p γ ga) n c) := by
        rw [← h1, map_sub, h2]
        simp only [ptw, Pi.sub_apply]
        rfl
      rw [e, ← hS, map_sub]
      exact S.sub_mem ((hS _).2 ((hgaC c).2 _)) ((hS _).2 ((hpcC c).2 _))
    rw [ptx_eq]
    exact isIntV_vecMul_inv hγ hdet hw b
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
