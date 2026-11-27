-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.mem_span_Pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:10.535018+00:00
-- url     : https://prove2.me/submissions/712aec4c-c8de-404d-b9d5-ff494ec00c67

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
import Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_apply
import Theorems.Thm_PositivityTheory_ThKH_Locrep_put_self
import Theorems.Thm_PositivityTheory_ThKH_Locrep_ev_put

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
variable {ev ι}
variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {g : A → ℂ} (hg : g ∈ SB A) :
    g ∈ Submodule.span ℂ {f | ∃ φ ∈ SB K, ∃ y, f = Pm ev ι φ y g} := by
  classical
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hπc : Continuous fun z : A => z - ι (ev z) := continuous_id.sub (hι.comp hev)
  have hKa : IsCompact ((fun z : A => z - ι (ev z)) '' tsupport g) := hg'.2.image hπc
  have hC : IsCompact (ev '' tsupport g) := hg'.2.image hev
  have hput_eq : ∀ x k, put ev ι x k = (x - ι (ev x)) + ι k := fun x k => rfl
  have hout : ∀ a k, ev a = 0 → a ∉ (fun z : A => z - ι (ev z)) '' tsupport g → g (a + ι k) = 0 := by
    intro a k ha hnot
    by_contra hne
    apply hnot
    refine ⟨a + ι k, subset_tsupport _ hne, ?_⟩
    simp [ha, h]
  have htube : ∀ k0 : K, ∀ᶠ k in 𝓝 k0, ∀ a ∈ (fun z : A => z - ι (ev z)) '' tsupport g,
      g (a + ι k) = g (a + ι k0) := by
    intro k0
    apply hKa.eventually_forall_of_forall_eventually
    intro a _
    have h1 : ∀ᶠ p in 𝓝 (k0, a), g (p.2 + ι p.1) = g (a + ι k0) :=
      ((continuous_snd.add (hι.comp continuous_fst)).tendsto (k0, a)).eventually
        (hg'.1.eventually_eq (a + ι k0))
    have h2 : ∀ᶠ p in 𝓝 (k0, a), g (p.2 + ι k0) = g (a + ι k0) :=
      ((continuous_snd.add continuous_const).tendsto (k0, a)).eventually
        (hg'.1.eventually_eq (a + ι k0))
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2]
  let F : K → A → ℂ := fun k x => g (put ev ι x k)
  have hFloc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k0
    filter_upwards [htube k0] with k hk
    funext x
    show g (put ev ι x k) = g (put ev ι x k0)
    rw [hput_eq, hput_eq]
    have hev0 : ev (x - ι (ev x)) = 0 := by simp [h]
    by_cases hx : x - ι (ev x) ∈ (fun z : A => z - ι (ev z)) '' tsupport g
    · exact hk _ hx
    · rw [hout _ _ hev0 hx, hout _ _ hev0 hx]
  have hFzero : ∀ k, k ∉ ev '' tsupport g → F k = 0 := by
    intro k hk
    funext x
    by_contra hne
    apply hk
    exact ⟨put ev ι x k, subset_tsupport _ hne, ev_put h x k⟩
  have hfin : (F '' (ev '' tsupport g)).Finite := by
    letI : TopologicalSpace (A → ℂ) := ⊥
    haveI : DiscreteTopology (A → ℂ) := ⟨rfl⟩
    exact (hC.image hFloc.continuous).finite_of_discrete
  let Vs : Finset (A → ℂ) := hfin.toFinset.filter (· ≠ 0)
  let rep : (A → ℂ) → K := fun v => if hv : ∃ k, F k = v then hv.choose else 0
  let φv : (A → ℂ) → K → ℂ := fun v k => if F k = v then 1 else 0
  have hrep : ∀ v ∈ Vs, F (rep v) = v := by
    intro v hv
    have hv' := (Finset.mem_filter.1 hv).1
    rw [Set.Finite.mem_toFinset] at hv'
    obtain ⟨k, _, hk⟩ := hv'
    have hex : ∃ k, F k = v := ⟨k, hk⟩
    show F (if hv : ∃ k, F k = v then hv.choose else 0) = v
    rw [dif_pos hex]
    exact hex.choose_spec
  have hφv : ∀ v ∈ Vs, φv v ∈ SB K := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_filter.1 hv).2
    refine ⟨hFloc.comp (fun w : A → ℂ => if w = v then (1 : ℂ) else 0), ?_⟩
    have hsupp : Function.support (φv v) ⊆ {k | F k = v} := by
      intro k hk
      by_contra hne
      exact hk (if_neg hne)
    have hL : {k | F k = v} ⊆ ev '' tsupport g := by
      intro k hk
      by_contra hc
      exact hv0 (hk.symm.trans (hFzero k hc))
    exact IsCompact.of_isClosed_subset hC (isClosed_tsupport _)
      ((closure_minimal hsupp (hFloc.isClosed_fiber v)).trans hL)
  have hsum : g = ∑ v ∈ Vs, Pm ev ι (φv v) (rep v) g := by
    funext x
    rw [Finset.sum_apply]
    have hterm : ∀ v ∈ Vs, Pm ev ι (φv v) (rep v) g x = if F (ev x) = v then v x else 0 := by
      intro v hv
      rw [Pm_apply]
      have hx : g (put ev ι x (rep v)) = v x := congrFun (hrep v hv) x
      rw [hx]
      show (if F (ev x) = v then (1 : ℂ) else 0) * v x = _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    have hgx : g x = F (ev x) x := by
      show g x = g (put ev ι x (ev x))
      rw [put_self]
    by_cases hmem : F (ev x) ∈ Vs
    · rw [if_pos hmem, ← hgx]
    · rw [if_neg hmem]
      have h0 : F (ev x) = 0 := by
        by_contra hne
        apply hmem
        have hc : ev x ∈ ev '' tsupport g := by
          by_contra hc
          exact hne (hFzero _ hc)
        exact Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset hfin).2 ⟨ev x, hc, rfl⟩, hne⟩
      rw [hgx, h0]
      rfl
  have hmem : (∑ v ∈ Vs, Pm ev ι (φv v) (rep v) g) ∈
      Submodule.span ℂ {f | ∃ φ ∈ SB K, ∃ y, f = Pm ev ι φ y g} :=
    Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨φv v, hφv v hv, rep v, rfl⟩
  rwa [← hsum] at hmem
end PositivityTheory.ThKH.Locrep
