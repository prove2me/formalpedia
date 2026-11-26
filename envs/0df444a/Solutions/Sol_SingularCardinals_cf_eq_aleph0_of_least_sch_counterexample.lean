-- Prove2me | solution 1 for SingularCardinals.cf_eq_aleph0_of_least_sch_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-26T03:09:17.191812+00:00
-- url     : https://prove2.me/submissions/0d4a6184-d153-41be-96e5-adcd663ce140

import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Tactic.NormNum
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic
import Theorems.Thm_JechSetTheory_pow_cof_eq_succ_of_isStationary
import Theorems.Thm_SingularCardinals_pow_cof_eq_two_pow_of_singular_strongLimit

universe u

open Cardinal Order Set JechSetTheory SingularCardinals

private lemma small_pow_lt {κ : Cardinal.{u}} (hsing : κ.IsSingular) (hlim : IsStrongLimit κ)
    {l : Cardinal.{u}} (hl : l < κ) : l ^ κ.ord.cof < κ := by
  have hcf_lt : κ.ord.cof < κ := hsing.cof_ord_lt
  have hℵ₀_lt : ℵ₀ < κ :=
    hsing.aleph0_le.lt_of_ne (fun h => not_isSingular_aleph0 (h ▸ hsing))
  have hcf_ne : κ.ord.cof ≠ 0 :=
    (Ordinal.cof_pos.2 (Cardinal.ord_pos.2 hsing.pos)).ne'
  by_cases hl0 : l = 0
  · rw [hl0, Cardinal.zero_power hcf_ne]
    exact hsing.pos
  · let m : Cardinal.{u} := max (max l κ.ord.cof) ℵ₀
    have hm_lt : m < κ := max_lt (max_lt hl hcf_lt) hℵ₀_lt
    have hm_inf : ℵ₀ ≤ m := le_max_right _ _
    have hl_le : l ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hcf_le : κ.ord.cof ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have h1 : l ^ κ.ord.cof ≤ m ^ κ.ord.cof := Cardinal.power_le_power_right hl_le
    have h2 : m ^ κ.ord.cof ≤ m ^ m :=
      Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hm_inf).ne' hcf_le
    calc
      l ^ κ.ord.cof ≤ m ^ m := h1.trans h2
      _ = 2 ^ m := Cardinal.power_self_eq hm_inf
      _ < κ := hlim.isStrongPrelimit hm_lt

private lemma noMaxOrder_below_of_aleph0_lt {c : Cardinal.{u}} (hcf : ℵ₀ < c) :
    NoMaxOrder (Below c) := by
  refine ⟨fun a => ?_⟩
  have hlim_ord : IsSuccLimit c.ord := Cardinal.isSuccLimit_ord hcf.le
  have hsucc_lt : Order.succ a.toOrd.1 < c.ord := hlim_ord.succ_lt a.toOrd.2
  refine ⟨Ordinal.ToType.mk ⟨Order.succ a.toOrd.1, hsucc_lt⟩, ?_⟩
  rw [← Ordinal.ToType.mk.symm.lt_iff_lt, Ordinal.ToType.mk.symm_apply_apply]
  exact Subtype.mk_lt_mk.mpr (Order.lt_succ a.toOrd.1)

private lemma nonempty_below_of_aleph0_lt {c : Cardinal.{u}} (hcf : ℵ₀ < c) :
    Nonempty (Below c) := by
  have hc_pos : 0 < c.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans hcf)
  exact ⟨Ordinal.ToType.mk ⟨0, hc_pos⟩⟩

private lemma isStationary_omega_limits {c : Cardinal.{u}}
    (hcf : ℵ₀ < c) (hreg : c.ord.cof = c) :
    IsStationary {x : Below c | ∃ seq : ℕ → Below c, StrictMono seq ∧ IsLUB (Set.range seq) x} := by
  have : Nonempty (Below c) := nonempty_below_of_aleph0_lt hcf
  have : NoMaxOrder (Below c) := noMaxOrder_below_of_aleph0_lt hcf
  let : OrderBot (Below c) := WellFoundedLT.toOrderBot (Below c)
  let : ConditionallyCompleteLinearOrderBot (Below c) :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot (Below c)
  intro C hC
  have hnext_ex : ∀ a : Below c, ∃ b ∈ C, a < b := by
    intro a
    obtain ⟨a', ha'⟩ := exists_gt a
    obtain ⟨b, hbC, hba'⟩ := hC.isCofinal a'
    exact ⟨b, hbC, ha'.trans_le hba'⟩
  choose next hnext_mem hnext_gt using hnext_ex
  obtain ⟨c₀, hc₀⟩ := hC.nonempty
  let seq : ℕ → Below c := fun n => next^[n] c₀
  have hseq_mem : ∀ n, seq n ∈ C := by
    intro n
    induction n with
    | zero => exact hc₀
    | succ n _ =>
      show next^[n + 1] c₀ ∈ C
      rw [Function.iterate_succ_apply']
      exact hnext_mem _
  have hseq_strict : StrictMono seq := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show next^[n] c₀ < next^[n + 1] c₀
    rw [Function.iterate_succ_apply']
    exact hnext_gt _
  have hseq_bdd : BddAbove (Set.range seq) := by
    refine BddAbove.of_not_isCofinal fun hcof => (Order.cof_le hcof).not_gt ?_
    rw [Ordinal.cof_toType, hreg]
    have hcard : #(Set.range seq) ≤ ℵ₀ := by
      have h1 := Cardinal.mk_range_le_lift (f := seq)
      simpa using h1
    exact hcard.trans_lt hcf
  let x : Below c := sSup (Set.range seq)
  have hlub : IsLUB (Set.range seq) x := isLUB_csSup (Set.range_nonempty seq) hseq_bdd
  have hxC : x ∈ C := hC.isLUB_mem (Set.range_subset_iff.2 hseq_mem) (Set.range_nonempty seq) hlub
  exact ⟨x, ⟨seq, hseq_strict, hlub⟩, hxC⟩

private lemma exists_normal_strongLimit_seq {κ : Cardinal.{u}}
    (hsing : κ.IsSingular) (hlim : IsStrongLimit κ) (hcf_gt : ℵ₀ < κ.ord.cof) :
    ∃ f : Below κ.ord.cof → Cardinal.{u},
      IsNormalCardinalSeq f ∧
      (⨆ x, f x) = κ ∧
      (∀ x, f x < κ) ∧
      (∀ x, ℵ₀ ≤ f x) ∧
      (∀ x, IsSuccLimit x → IsStrongLimit (f x)) := by
  classical
  set c := κ.ord.cof
  have : Nonempty (Below c) := nonempty_below_of_aleph0_lt hcf_gt
  have : NoMaxOrder (Below c) := noMaxOrder_below_of_aleph0_lt hcf_gt
  have hℵ₀_lt_κ : ℵ₀ < κ := hcf_gt.trans hsing.cof_ord_lt
  obtain ⟨f₀, hf₀⟩ := Ordinal.exists_isFundamentalSeq (o := κ.ord) rfl
  let g : Below c → Cardinal.{u} := fun x => (f₀ x.toOrd).1.card
  have hg_mono : Monotone g := by
    intro x y hxy
    have h1 : x.toOrd ≤ y.toOrd := Ordinal.ToType.mk.symm.monotone hxy
    exact Ordinal.card_le_card (hf₀.strictMono.monotone h1)
  have hg_lt : ∀ x, g x < κ := by
    intro x
    exact Cardinal.lt_ord.mp (f₀ x.toOrd).2
  have hg_sup : (⨆ x, g x) = κ := by
    apply le_antisymm
    · exact ciSup_le fun x => (hg_lt x).le
    · refine le_of_forall_lt fun μ hμ => ?_
      have hμ_succ : Order.succ μ < κ := hsing.isSuccLimit.succ_lt hμ
      have hord : (Order.succ μ).ord < κ.ord := Cardinal.ord_lt_ord.2 hμ_succ
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf₀.isCofinal_range ⟨(Order.succ μ).ord, hord⟩
      let x : Below c := Ordinal.ToType.mk i
      have hx_toOrd : x.toOrd = i := Ordinal.ToType.mk.symm_apply_apply i
      have hle : Order.succ μ ≤ g x := by
        calc
          Order.succ μ = (Order.succ μ).ord.card := (Cardinal.card_ord _).symm
          _ ≤ (f₀ i).1.card := Ordinal.card_le_card hi
          _ = g x := by simp [g, hx_toOrd]
      exact (Order.lt_succ μ).trans_le (hle.trans (le_ciSup Cardinal.bddAbove_of_small x))
  let f : Below c → Cardinal.{u} := WellFoundedLT.fix fun x ih =>
    if IsSuccLimit x then
      ⨆ y : Set.Iio x, ih y.1 y.2
    else
      max (max ℵ₀ (g x)) (⨆ y : Set.Iio x, Order.succ (2 ^ ih y.1 y.2))
  have hf_lim : ∀ x, IsSuccLimit x → f x = ⨆ y : Set.Iio x, f y := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_nonlim : ∀ x, ¬ IsSuccLimit x →
      f x = max (max ℵ₀ (g x)) (⨆ y : Set.Iio x, Order.succ (2 ^ f y)) := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_lt : ∀ x, f x < κ := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x ih =>
      have hcard_lt : #(Set.Iio x) < c := by
        simpa [c] using Cardinal.mk_Iio_lt x (by simp)
      by_cases hx : IsSuccLimit x
      · rw [hf_lim x hx]
        exact Cardinal.iSup_lt_of_lt_cof_ord hcard_lt fun y => ih y.1 y.2
      · rw [hf_nonlim x hx]
        refine max_lt (max_lt hℵ₀_lt_κ (hg_lt x)) ?_
        refine Cardinal.iSup_lt_of_lt_cof_ord hcard_lt fun y => ?_
        exact hsing.isSuccLimit.succ_lt (hlim.isStrongPrelimit (ih y.1 y.2))
  have hf_pow_le_nonlim : ∀ {y x : Below c}, y < x → ¬ IsSuccLimit x →
      Order.succ (2 ^ f y) ≤ f x := by
    intro y x hyx hx
    rw [hf_nonlim x hx]
    have hle : Order.succ ((2 : Cardinal.{u}) ^ f y) ≤
        ⨆ z : Set.Iio x, Order.succ ((2 : Cardinal.{u}) ^ f z.1) :=
      le_ciSup (f := fun z : Set.Iio x => Order.succ ((2 : Cardinal.{u}) ^ f z.1))
        Cardinal.bddAbove_of_small ⟨y, hyx⟩
    exact hle.trans (le_max_right _ _)
  have hf_strict : StrictMono f := by
    intro y x hyx
    by_cases hx : IsSuccLimit x
    · have hsy_lt : Order.succ y < x := hx.succ_lt hyx
      have hy_lt_sy : y < Order.succ y := Order.lt_succ y
      have hsy_not_lim : ¬ IsSuccLimit (Order.succ y) := fun h => not_isMax y h.isMax
      have h1 : f y < f (Order.succ y) :=
        ((Cardinal.cantor (f y)).trans (Order.lt_succ _)).trans_le (hf_pow_le_nonlim hy_lt_sy hsy_not_lim)
      have h2 : f (Order.succ y) ≤ f x := by
        rw [hf_lim x hx]
        exact le_ciSup (f := fun z : Set.Iio x => f z.1)
          Cardinal.bddAbove_of_small ⟨Order.succ y, hsy_lt⟩
      exact h1.trans_le h2
    · exact ((Cardinal.cantor (f y)).trans (Order.lt_succ _)).trans_le (hf_pow_le_nonlim hyx hx)
  have hf_aleph0 : ∀ x, ℵ₀ ≤ f x := by
    intro x
    by_cases hx : IsSuccLimit x
    · have hc_pos : 0 < c.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans hcf_gt)
      let b : Below c := Ordinal.ToType.mk ⟨0, hc_pos⟩
      have hb_le_all : ∀ z : Below c, b ≤ z := by
        intro z
        rw [← Ordinal.ToType.mk.symm.le_iff_le, Ordinal.ToType.mk.symm_apply_apply]
        exact Subtype.mk_le_mk.mpr bot_le
      have hb_min : IsMin b := fun z _ => hb_le_all z
      have hb_not_lim : ¬ IsSuccLimit b := fun h => h.not_isMin hb_min
      have hb_lt_x : b < x :=
        (hb_le_all x).lt_of_ne (fun h => hx.not_isMin (h ▸ hb_min))
      have hb_ge : ℵ₀ ≤ f b := by
        rw [hf_nonlim b hb_not_lim]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      exact hb_ge.trans (hf_strict hb_lt_x).le
    · rw [hf_nonlim x hx]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hf_strongLim : ∀ x, IsSuccLimit x → IsStrongLimit (f x) := by
    intro x hx
    refine ⟨(Cardinal.aleph0_pos.trans_le (hf_aleph0 x)).ne', fun ρ hρ => ?_⟩
    rw [hf_lim x hx] at hρ
    obtain ⟨y₀, hy₀⟩ := not_isMin_iff.mp hx.not_isMin
    have : Nonempty (Set.Iio x) := ⟨⟨y₀, hy₀⟩⟩
    obtain ⟨y, hy⟩ := (lt_ciSup_iff Cardinal.bddAbove_of_small).mp hρ
    have hsy_lt : Order.succ y.1 < x := hx.succ_lt y.2
    have hy_lt_sy : y.1 < Order.succ y.1 := Order.lt_succ y.1
    have hsy_not_lim : ¬ IsSuccLimit (Order.succ y.1) := fun h => not_isMax y.1 h.isMax
    have h1 : (2 : Cardinal.{u}) ^ ρ ≤ (2 : Cardinal.{u}) ^ f y.1 :=
      Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{u}) ≠ 0) hy.le
    have h2 : (2 : Cardinal.{u}) ^ f y.1 < f (Order.succ y.1) :=
      (Order.lt_succ _).trans_le (hf_pow_le_nonlim hy_lt_sy hsy_not_lim)
    exact (h1.trans_lt h2).trans (hf_strict hsy_lt)
  have hf_sup : (⨆ x, f x) = κ := by
    apply le_antisymm
    · exact ciSup_le fun x => (hf_lt x).le
    · rw [← hg_sup]
      refine ciSup_le fun x => ?_
      have hsx_not_lim : ¬ IsSuccLimit (Order.succ x) := fun h => not_isMax x h.isMax
      have h1 : g x ≤ g (Order.succ x) := hg_mono (Order.le_succ x)
      have h2 : g (Order.succ x) ≤ f (Order.succ x) := by
        rw [hf_nonlim (Order.succ x) hsx_not_lim]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact (h1.trans h2).trans (le_ciSup Cardinal.bddAbove_of_small (Order.succ x))
  exact ⟨f, ⟨hf_strict, hf_lim⟩, hf_sup, hf_lt, hf_aleph0, hf_strongLim⟩

theorem solution (κ : Cardinal.{u})
    (hsing : κ.IsSingular) (hlim : IsStrongLimit κ) (hfail : 2 ^ κ ≠ Order.succ κ)
    (hleast : ∀ μ : Cardinal.{u}, μ < κ → μ.IsSingular → IsStrongLimit μ →
      2 ^ μ = Order.succ μ) :
    κ.ord.cof = ℵ₀ := by
  by_contra hcf_ne
  have hcf_ge : ℵ₀ ≤ κ.ord.cof :=
    Ordinal.aleph0_le_cof_iff.mpr (Ordinal.one_lt_cof_iff.mpr (Cardinal.isSuccLimit_ord hsing.aleph0_le))
  have hcf_gt : ℵ₀ < κ.ord.cof := hcf_ge.lt_of_ne' hcf_ne
  have hsmall : ∀ l < κ, l ^ κ.ord.cof < κ := fun l hl => small_pow_lt hsing hlim hl
  obtain ⟨f, hf_normal, hf_sup, hf_lt, hf_aleph0, hf_strongLim⟩ :=
    exists_normal_strongLimit_seq hsing hlim hcf_gt
  have hS_stat : IsStationary
      {x : Below κ.ord.cof | ∃ seq : ℕ → Below κ.ord.cof, StrictMono seq ∧ IsLUB (Set.range seq) x} :=
    isStationary_omega_limits hcf_gt (Ordinal.cof_ord_cof κ.ord)
  have hgood_stat : IsStationary
      {x : Below κ.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)} := by
    refine hS_stat.mono ?_
    rintro x ⟨seq, hstrict, hlub⟩
    have hseq_lt : ∀ n, seq n < x := fun n =>
      (hstrict (Nat.lt_succ_self n)).trans_le (hlub.1 ⟨n + 1, rfl⟩)
    have hx_lim : IsSuccLimit x := by
      refine ⟨fun hmin => (hseq_lt 0).not_ge (hmin (hseq_lt 0).le), fun y hcov => ?_⟩
      have hnot_ub : ¬ y ∈ upperBounds (Set.range seq) :=
        fun hub => hcov.1.not_ge (hlub.2 hub)
      rw [mem_upperBounds] at hnot_ub
      push Not at hnot_ub
      obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnot_ub
      exact hcov.2 hn (hseq_lt n)
    have hfx_lim : IsStrongLimit (f x) := hf_strongLim x hx_lim
    have hfx_gt_aleph0 : ℵ₀ < f x := (hf_aleph0 (seq 0)).trans_lt (hf_normal.1 (hseq_lt 0))
    have hfx_sup_seq : (⨆ n : ℕ, f (seq n)) = f x := by
      have : Nonempty (Set.Iio x) := ⟨⟨seq 0, hseq_lt 0⟩⟩
      apply le_antisymm
      · exact ciSup_le fun n => (hf_normal.1 (hseq_lt n)).le
      · rw [hf_normal.2 x hx_lim]
        refine ciSup_le fun y => ?_
        have hnot_ub : ¬ y.1 ∈ upperBounds (Set.range seq) :=
          fun hub => y.2.not_ge (hlub.2 hub)
        rw [mem_upperBounds] at hnot_ub
        push Not at hnot_ub
        obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnot_ub
        exact (hf_normal.1 hn).le.trans (le_ciSup Cardinal.bddAbove_of_small n)
    have hfx_cof_le : (f x).ord.cof ≤ ℵ₀ := by
      by_contra! hgt
      have hlt := Cardinal.lift_iSup_lt_of_lt_cof_ord (f := fun n : ℕ => f (seq n)) (a := f x)
        (by simpa using hgt) (fun n => hf_normal.1 (hseq_lt n))
      exact hlt.ne hfx_sup_seq
    have hfx_sing : (f x).IsSingular :=
      ⟨hfx_gt_aleph0.le, (hfx_cof_le.trans_lt hfx_gt_aleph0).ne⟩
    have h2 : 2 ^ f x = Order.succ (f x) := hleast (f x) (hf_lt x) hfx_sing hfx_lim
    have hbridge := SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit (f x) hfx_sing hfx_lim
    exact hbridge.trans h2
  have hpow : κ ^ κ.ord.cof = Order.succ κ :=
    JechSetTheory.pow_cof_eq_succ_of_isStationary κ hsing hcf_gt hsmall f hf_normal hf_sup hgood_stat
  have hbridge_κ : κ ^ κ.ord.cof = 2 ^ κ :=
    SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit κ hsing hlim
  exact hfail (hbridge_κ.symm.trans hpow)
