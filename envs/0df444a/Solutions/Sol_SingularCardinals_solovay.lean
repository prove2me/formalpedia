-- Prove2me | solution 1 for SingularCardinals.solovay
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-27T02:41:09.212316+00:00
-- url     : https://prove2.me/submissions/241462ef-7bb5-4aaa-beee-1a7c55a4ee01

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Tactic.NormNum
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_largeCardinals
import Theorems.Thm_JechSetTheory_pow_cof_eq_succ_of_isStationary
import Theorems.Thm_SingularCardinals_pow_cof_eq_two_pow_of_singular_strongLimit

universe u

open Cardinal Order Set JechSetTheory SingularCardinals

private lemma small_pow_lt {μ : Cardinal.{u}} (hsing : μ.IsSingular) (hlim : IsStrongLimit μ)
    {l : Cardinal.{u}} (hl : l < μ) : l ^ μ.ord.cof < μ := by
  have hcf_lt : μ.ord.cof < μ := hsing.cof_ord_lt
  have hℵ₀_lt : ℵ₀ < μ :=
    hsing.aleph0_le.lt_of_ne (fun h => not_isSingular_aleph0 (h ▸ hsing))
  have hcf_ne : μ.ord.cof ≠ 0 :=
    (Ordinal.cof_pos.2 (Cardinal.ord_pos.2 hsing.pos)).ne'
  by_cases hl0 : l = 0
  · rw [hl0, Cardinal.zero_power hcf_ne]
    exact hsing.pos
  · let m : Cardinal.{u} := max (max l μ.ord.cof) ℵ₀
    have hm_lt : m < μ := max_lt (max_lt hl hcf_lt) hℵ₀_lt
    have hm_inf : ℵ₀ ≤ m := le_max_right _ _
    have hl_le : l ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hcf_le : μ.ord.cof ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have h1 : l ^ μ.ord.cof ≤ m ^ μ.ord.cof := Cardinal.power_le_power_right hl_le
    have h2 : m ^ μ.ord.cof ≤ m ^ m :=
      Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hm_inf).ne' hcf_le
    calc
      l ^ μ.ord.cof ≤ m ^ m := h1.trans h2
      _ = 2 ^ m := Cardinal.power_self_eq hm_inf
      _ < μ := hlim.isStrongPrelimit hm_lt

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

private lemma exists_normal_strongLimit_seq_above {κ μ : Cardinal.{u}}
    (hκ_lt : κ < μ) (hsing : μ.IsSingular) (hlim : IsStrongLimit μ) (hcf_gt : ℵ₀ < μ.ord.cof) :
    ∃ f : Below μ.ord.cof → Cardinal.{u},
      IsNormalCardinalSeq f ∧
      (⨆ x, f x) = μ ∧
      (∀ x, f x < μ) ∧
      (∀ x, κ < f x) ∧
      (∀ x, ℵ₀ ≤ f x) ∧
      (∀ x, IsSuccLimit x → IsStrongLimit (f x)) := by
  classical
  set c := μ.ord.cof
  have : Nonempty (Below c) := nonempty_below_of_aleph0_lt hcf_gt
  have : NoMaxOrder (Below c) := noMaxOrder_below_of_aleph0_lt hcf_gt
  have hℵ₀_lt_μ : ℵ₀ < μ := hcf_gt.trans hsing.cof_ord_lt
  have hbase_lt : max ℵ₀ (Order.succ κ) < μ :=
    max_lt hℵ₀_lt_μ (hsing.isSuccLimit.succ_lt hκ_lt)
  obtain ⟨f₀, hf₀⟩ := Ordinal.exists_isFundamentalSeq (o := μ.ord) rfl
  let g : Below c → Cardinal.{u} := fun x => (f₀ x.toOrd).1.card
  have hg_mono : Monotone g := by
    intro x y hxy
    have h1 : x.toOrd ≤ y.toOrd := Ordinal.ToType.mk.symm.monotone hxy
    exact Ordinal.card_le_card (hf₀.strictMono.monotone h1)
  have hg_lt : ∀ x, g x < μ := by
    intro x
    exact Cardinal.lt_ord.mp (f₀ x.toOrd).2
  have hg_sup : (⨆ x, g x) = μ := by
    apply le_antisymm
    · exact ciSup_le fun x => (hg_lt x).le
    · refine le_of_forall_lt fun ν hν => ?_
      have hν_succ : Order.succ ν < μ := hsing.isSuccLimit.succ_lt hν
      have hord : (Order.succ ν).ord < μ.ord := Cardinal.ord_lt_ord.2 hν_succ
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf₀.isCofinal_range ⟨(Order.succ ν).ord, hord⟩
      let x : Below c := Ordinal.ToType.mk i
      have hx_toOrd : x.toOrd = i := Ordinal.ToType.mk.symm_apply_apply i
      have hle : Order.succ ν ≤ g x := by
        calc
          Order.succ ν = (Order.succ ν).ord.card := (Cardinal.card_ord _).symm
          _ ≤ (f₀ i).1.card := Ordinal.card_le_card hi
          _ = g x := by simp [g, hx_toOrd]
      exact (Order.lt_succ ν).trans_le (hle.trans (le_ciSup Cardinal.bddAbove_of_small x))
  let f : Below c → Cardinal.{u} := WellFoundedLT.fix fun x ih =>
    if IsSuccLimit x then
      ⨆ y : Set.Iio x, ih y.1 y.2
    else
      max (max (max ℵ₀ (Order.succ κ)) (g x)) (⨆ y : Set.Iio x, Order.succ (2 ^ ih y.1 y.2))
  have hf_lim : ∀ x, IsSuccLimit x → f x = ⨆ y : Set.Iio x, f y := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_nonlim : ∀ x, ¬ IsSuccLimit x →
      f x = max (max (max ℵ₀ (Order.succ κ)) (g x)) (⨆ y : Set.Iio x, Order.succ (2 ^ f y)) := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_lt : ∀ x, f x < μ := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x ih =>
      have hcard_lt : #(Set.Iio x) < c := by
        simpa [c] using Cardinal.mk_Iio_lt x (by simp)
      by_cases hx : IsSuccLimit x
      · rw [hf_lim x hx]
        exact Cardinal.iSup_lt_of_lt_cof_ord hcard_lt fun y => ih y.1 y.2
      · rw [hf_nonlim x hx]
        refine max_lt (max_lt hbase_lt (hg_lt x)) ?_
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
  have hf_base : ∀ x, max ℵ₀ (Order.succ κ) ≤ f x := by
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
      have hb_ge : max ℵ₀ (Order.succ κ) ≤ f b := by
        rw [hf_nonlim b hb_not_lim]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      exact hb_ge.trans (hf_strict hb_lt_x).le
    · rw [hf_nonlim x hx]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hf_gt_κ : ∀ x, κ < f x := fun x =>
    (Order.lt_succ κ).trans_le ((le_max_right _ _).trans (hf_base x))
  have hf_aleph0 : ∀ x, ℵ₀ ≤ f x := fun x =>
    (le_max_left _ _).trans (hf_base x)
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
  have hf_sup : (⨆ x, f x) = μ := by
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
  exact ⟨f, ⟨hf_strict, hf_lim⟩, hf_sup, hf_lt, hf_gt_κ, hf_aleph0, hf_strongLim⟩

private lemma solovay_of_cof_aleph0 {κ : Cardinal.{u}} (hκ : IsStronglyCompact κ)
    {μ : Cardinal.{u}} (hμ : κ < μ) (hsing : μ.IsSingular) (hlim : IsStrongLimit μ)
    (hcf : μ.ord.cof = ℵ₀) :
    2 ^ μ = Order.succ μ := by
  classical
  apply le_antisymm _ (Order.succ_le_of_lt (Cardinal.cantor μ))
  have hbridge : μ ^ μ.ord.cof = 2 ^ μ :=
    SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit μ hsing hlim
  rw [← hbridge, hcf]
  let lam : Cardinal.{u} := Order.succ μ
  have hℵ₀_lt_μ : ℵ₀ < μ := hκ.1.trans hμ
  have hℵ₀_lt_lam : ℵ₀ < lam := hℵ₀_lt_μ.trans (Order.lt_succ μ)
  have hlam_reg : lam.IsRegular := Cardinal.isRegular_succ hsing.aleph0_le
  have hlam_cof : lam.ord.cof = lam := hlam_reg.cof_ord
  let X : Type u := Below lam
  have : Nonempty X := nonempty_below_of_aleph0_lt hℵ₀_lt_lam
  have : NoMaxOrder X := noMaxOrder_below_of_aleph0_lt hℵ₀_lt_lam
  -- Step 1: extend `Filter.atTop` on `Below (Order.succ μ)` to a `κ`-complete uniform ultrafilter `U`.
  have hF_neBot : (Filter.atTop : Filter X).NeBot := Filter.atTop_neBot
  have hF_comp : IsComplete κ (Filter.atTop : Filter X) := by
    intro ι s hι hs
    choose a ha using fun i => Filter.mem_atTop_sets.mp (hs i)
    have hbdd : BddAbove (Set.range a) := by
      refine BddAbove.of_not_isCofinal fun hcof => (Order.cof_le hcof).not_gt ?_
      rw [Ordinal.cof_toType, hlam_cof]
      exact (Cardinal.mk_range_le (f := a)).trans_lt (hι.trans (hμ.trans (Order.lt_succ μ)))
    obtain ⟨b, hb⟩ := hbdd
    refine Filter.mem_atTop_sets.mpr ⟨b, fun x hxb => ?_⟩
    exact Set.mem_iInter.mpr fun i => ha i x ((hb ⟨i, rfl⟩).trans hxb)
  obtain ⟨U, hU_comp, hU_le⟩ := hκ.2 X Filter.atTop hF_neBot hF_comp
  have hIoi_mem : ∀ γ : X, Set.Ioi γ ∈ U := by
    intro γ
    obtain ⟨γ', hγ'⟩ := exists_gt γ
    exact hU_le (Filter.mem_atTop_sets.mpr ⟨γ', fun x hx => hγ'.trans_le hx⟩)
  have hU_iUnion : ∀ S : ℕ → Set X, (⋃ n : ℕ, S n) ∈ U → ∃ n : ℕ, S n ∈ U := by
    intro S hS
    by_contra h
    push Not at h
    have hcompl : ∀ k : ULift.{u} ℕ, (S k.down)ᶜ ∈ (U : Filter X) := fun k =>
      Ultrafilter.compl_mem_iff_notMem.mpr (h k.down)
    have hcard : #(ULift.{u} ℕ) < κ := by simpa using hκ.1
    have hinter : (⋂ k : ULift.{u} ℕ, (S k.down)ᶜ) ∈ (U : Filter X) :=
      hU_comp (ULift.{u} ℕ) (fun k => (S k.down)ᶜ) hcard hcompl
    have hsub : (⋂ k : ULift.{u} ℕ, (S k.down)ᶜ) ⊆ (⋃ n : ℕ, S n)ᶜ := by
      intro x hx hxU
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxU
      exact (Set.mem_iInter.mp hx ⟨n⟩) hn
    have hcomplU : (⋃ n : ℕ, S n)ᶜ ∈ U := Filter.mem_of_superset hinter hsub
    exact (Ultrafilter.compl_mem_iff_notMem.mp hcomplU) hS
  -- Step 2: countable cofinal ladder `c : ℕ → Ordinal.{u}` below `μ.ord` and covering shelves `K n β`.
  obtain ⟨f₀, hf₀⟩ := Ordinal.exists_isFundamentalSeq (o := μ.ord) rfl
  have hord_cof : μ.ord.cof.ord = Ordinal.omega0 := by rw [hcf, Cardinal.ord_aleph0]
  let c : ℕ → Ordinal.{u} := fun n =>
    (f₀ ⟨(n : Ordinal.{u}), by rw [Set.mem_Iio, hord_cof]; exact Ordinal.natCast_lt_omega0 n⟩).1
  have hc_lt : ∀ n : ℕ, c n < μ.ord := fun n =>
    (f₀ ⟨(n : Ordinal.{u}), by rw [Set.mem_Iio, hord_cof]; exact Ordinal.natCast_lt_omega0 n⟩).2
  have hc_cof : ∀ ξ : Ordinal.{u}, ξ < μ.ord → ∃ n : ℕ, ξ < c n := by
    intro ξ hξ
    have hsucc_lt : Order.succ ξ < μ.ord := (Cardinal.isSuccLimit_ord hsing.aleph0_le).succ_lt hξ
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf₀.isCofinal_range ⟨Order.succ ξ, hsucc_lt⟩
    have hi_lt : i.1 < Ordinal.omega0 := lt_of_lt_of_eq i.2 hord_cof
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hi_lt
    have hi_eq : i = ⟨(n : Ordinal.{u}), by rw [Set.mem_Iio, hord_cof]; exact Ordinal.natCast_lt_omega0 n⟩ :=
      Subtype.ext hn
    have hi_le : Order.succ ξ ≤ (f₀ i).1 := hi
    rw [hi_eq] at hi_le
    exact ⟨n, (Order.lt_succ ξ).trans_le hi_le⟩
  have hφ_nonempty : ∀ β : X, Nonempty (Set.Iio β ↪ μ.ord.ToType) := by
    intro β
    apply (Cardinal.le_def _ _).mp
    have h1 : #(Set.Iio β) ≤ #(β.toOrd.1.ToType) := by
      let g : Set.Iio β → β.toOrd.1.ToType := fun x =>
        Ordinal.ToType.mk ⟨x.1.toOrd.1, Set.mem_Iio.mpr (Ordinal.ToType.mk.symm.lt_iff_lt.mpr x.2)⟩
      have hg_inj : Function.Injective g := by
        intro x₁ x₂ hEq
        have hsub := Ordinal.ToType.mk.injective hEq
        have hval : x₁.1.toOrd.1 = x₂.1.toOrd.1 :=
          congrArg (fun z : Set.Iio β.toOrd.1 => z.1) hsub
        exact Subtype.ext (Ordinal.ToType.mk.symm.injective (Subtype.ext hval))
      exact Cardinal.mk_le_of_injective hg_inj
    have h2 : β.toOrd.1.card ≤ μ := Order.lt_succ_iff.mp (Cardinal.lt_ord.mp β.toOrd.2)
    calc
      #(Set.Iio β) ≤ #(β.toOrd.1.ToType) := h1
      _ = β.toOrd.1.card := Cardinal.mk_toType _
      _ ≤ μ := h2
      _ = #(μ.ord.ToType) := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  let φ : ∀ β : X, Set.Iio β ↪ μ.ord.ToType := fun β => Classical.choice (hφ_nonempty β)
  let K (n : ℕ) (β : X) : Set X := {γ : X | ∃ h : γ < β, (φ β ⟨γ, h⟩).toOrd.1 < c n}
  have hK_cover : ∀ {γ β : X}, γ < β → ∃ n : ℕ, γ ∈ K n β := by
    intro γ β hlt
    obtain ⟨n, hn⟩ := hc_cof (φ β ⟨γ, hlt⟩).toOrd.1 (φ β ⟨γ, hlt⟩).toOrd.2
    exact ⟨n, hlt, hn⟩
  have hK_card : ∀ n β, #(K n β) ≤ (c n).card := by
    intro n β
    let g : K n β → (c n).ToType := fun γ =>
      Ordinal.ToType.mk ⟨(φ β ⟨γ.1, γ.2.1⟩).toOrd.1, γ.2.2⟩
    have hg_inj : Function.Injective g := by
      intro γ₁ γ₂ hEq
      have hsub := Ordinal.ToType.mk.injective hEq
      have hval : (φ β ⟨γ₁.1, γ₁.2.1⟩).toOrd.1 = (φ β ⟨γ₂.1, γ₂.2.1⟩).toOrd.1 :=
        congrArg (fun z : Set.Iio (c n) => z.1) hsub
      have hφ_eq := Ordinal.ToType.mk.symm.injective (Subtype.ext hval)
      have hIio_eq := (φ β).injective hφ_eq
      exact Subtype.ext (congrArg (fun z : Set.Iio β => z.1) hIio_eq)
    calc
      #(K n β) ≤ #((c n).ToType) := Cardinal.mk_le_of_injective hg_inj
      _ = (c n).card := Cardinal.mk_toType _
  -- Step 3: double voting with `U` finds a master shelf index `n₀` and an unbounded set `B n₀ ∈ U`.
  let A (n : ℕ) (γ : X) : Set X := {β : X | γ < β ∧ γ ∈ K n β}
  have hA_ex : ∀ γ : X, ∃ n : ℕ, A n γ ∈ U := by
    intro γ
    apply hU_iUnion (fun n => A n γ)
    refine Filter.mem_of_superset (hIoi_mem γ) ?_
    intro β hβ
    obtain ⟨n, hn⟩ := hK_cover hβ
    exact Set.mem_iUnion.mpr ⟨n, hβ, hn⟩
  let B (n : ℕ) : Set X := {γ : X | A n γ ∈ U}
  have hB_univ : (⋃ n : ℕ, B n) = Set.univ := by
    ext γ
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hA_ex γ
  obtain ⟨n₀, hB₀⟩ := hU_iUnion B (by rw [hB_univ]; exact Filter.univ_mem)
  have hμ_le_B : μ ≤ #(B n₀) := by
    have hlam_le : lam ≤ #(B n₀) := by
      by_contra hlt
      have hcard_lt : #(B n₀) < lam := lt_of_not_ge hlt
      have hbdd : BddAbove (B n₀) := by
        refine BddAbove.of_not_isCofinal fun hcof => (Order.cof_le hcof).not_gt ?_
        rw [Ordinal.cof_toType, hlam_cof]
        exact hcard_lt
      obtain ⟨b, hb⟩ := hbdd
      obtain ⟨γ, hγ_gt, hγ_B⟩ := U.nonempty_of_mem (Filter.inter_mem (hIoi_mem b) hB₀)
      exact hγ_gt.not_ge (hb hγ_B)
    exact (Order.le_succ μ).trans hlam_le
  -- Step 4: every countable sequence in `B n₀` is caught inside a single shelf `K n₀ β`.
  let S (β : X) : Set (ULift.{u} ℕ → B n₀) := {f | ∀ k, (f k).1 ∈ K n₀ β}
  have hS_univ : (⋃ β : X, S β) = Set.univ := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hf_mem : ∀ k : ULift.{u} ℕ, A n₀ (f k).1 ∈ (U : Filter X) := fun k => (f k).2
    have hcard : #(ULift.{u} ℕ) < κ := by simpa using hκ.1
    have hinter : (⋂ k : ULift.{u} ℕ, A n₀ (f k).1) ∈ U :=
      hU_comp (ULift.{u} ℕ) (fun k => A n₀ (f k).1) hcard hf_mem
    obtain ⟨β, hβ⟩ := U.nonempty_of_mem hinter
    exact ⟨β, fun k => (Set.mem_iInter.mp hβ k).2⟩
  have hS_lt : ∀ β : X, #(S β) < μ := by
    intro β
    let g : S β → (ULift.{u} ℕ → K n₀ β) := fun f k => ⟨(f.1 k).1, f.2 k⟩
    have hg_inj : Function.Injective g := by
      intro f₁ f₂ hEq
      apply Subtype.ext
      funext k
      have hk := congrFun hEq k
      exact Subtype.ext (congrArg (fun z : K n₀ β => z.1) hk)
    let m : Cardinal.{u} := max (c n₀).card ℵ₀
    have hm_lt : m < μ := max_lt (Cardinal.lt_ord.mp (hc_lt n₀)) hℵ₀_lt_μ
    have hm_inf : ℵ₀ ≤ m := le_max_right _ _
    have hK_le_m : #(K n₀ β) ≤ m := (hK_card n₀ β).trans (le_max_left _ _)
    calc
      #(S β) ≤ #(ULift.{u} ℕ → K n₀ β) := Cardinal.mk_le_of_injective hg_inj
      _ = (#(K n₀ β)) ^ ℵ₀ := by simp
      _ ≤ m ^ ℵ₀ := Cardinal.power_le_power_right hK_le_m
      _ ≤ m ^ m := Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hm_inf).ne' hm_inf
      _ = 2 ^ m := Cardinal.power_self_eq hm_inf
      _ < μ := hlim.isStrongPrelimit hm_lt
  -- Step 5: count all countable sequences in `B n₀` across the `lam = μ⁺` shelves.
  calc
    μ ^ ℵ₀ ≤ (#(B n₀)) ^ ℵ₀ := Cardinal.power_le_power_right hμ_le_B
    _ = #(ULift.{u} ℕ → B n₀) := by simp
    _ = #(⋃ β : X, S β) := by rw [hS_univ, Cardinal.mk_univ]
    _ ≤ Cardinal.sum (fun β : X => #(S β)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : X => μ) := Cardinal.sum_le_sum _ _ (fun β => (hS_lt β).le)
    _ = #X * μ := by simp [Cardinal.sum_const]
    _ = lam * μ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
    _ = lam := Cardinal.mul_eq_left hℵ₀_lt_lam.le (Order.le_succ μ)
      (Cardinal.aleph0_pos.trans hℵ₀_lt_μ).ne'

theorem solution (κ : Cardinal.{u}) (hκ : IsStronglyCompact κ) (μ : Cardinal.{u})
    (hμ : κ < μ) (hsing : μ.IsSingular) (hlim : IsStrongLimit μ) :
    2 ^ μ = Order.succ μ := by
  revert hμ hsing hlim
  induction μ using WellFoundedLT.induction with
  | ind μ ih =>
    intro hμ hsing hlim
    by_contra hfail
    have hcf_ge : ℵ₀ ≤ μ.ord.cof :=
      Ordinal.aleph0_le_cof_iff.mpr
        (Ordinal.one_lt_cof_iff.mpr (Cardinal.isSuccLimit_ord hsing.aleph0_le))
    by_cases hcf : μ.ord.cof = ℵ₀
    · exact hfail (solovay_of_cof_aleph0 hκ hμ hsing hlim hcf)
    · have hcf_gt : ℵ₀ < μ.ord.cof := hcf_ge.lt_of_ne' hcf
      have hsmall : ∀ l < μ, l ^ μ.ord.cof < μ := fun l hl => small_pow_lt hsing hlim hl
      obtain ⟨f, hf_normal, hf_sup, hf_lt, hf_gt_κ, hf_aleph0, hf_strongLim⟩ :=
        exists_normal_strongLimit_seq_above hμ hsing hlim hcf_gt
      have hS_stat : IsStationary
          {x : Below μ.ord.cof | ∃ seq : ℕ → Below μ.ord.cof, StrictMono seq ∧ IsLUB (Set.range seq) x} :=
        isStationary_omega_limits hcf_gt (Ordinal.cof_ord_cof μ.ord)
      have hgood_stat : IsStationary
          {x : Below μ.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)} := by
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
        have h2 : 2 ^ f x = Order.succ (f x) := ih (f x) (hf_lt x) (hf_gt_κ x) hfx_sing hfx_lim
        have hbridge :=
          SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit (f x) hfx_sing hfx_lim
        exact hbridge.trans h2
      have hpow : μ ^ μ.ord.cof = Order.succ μ :=
        JechSetTheory.pow_cof_eq_succ_of_isStationary μ hsing hcf_gt hsmall f hf_normal hf_sup hgood_stat
      have hbridge_μ : μ ^ μ.ord.cof = 2 ^ μ :=
        SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit μ hsing hlim
      exact hfail (hbridge_μ.symm.trans hpow)
