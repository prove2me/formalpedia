-- Prove2me | solution 1 for Supermodularity.Games.exists_monotone_greatest_least_equilibrium_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:12:06.262309+00:00
-- url     : https://prove2.me/submissions/862eb86e-2a94-44b8-9ae2-bcca7f1660cb

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

set_option autoImplicit false

namespace P801

open Supermodularity.Games Supermodularity.Monotonicity Supermodularity.Lattices

theorem exists_greatest_of_supClosed {X : Type*} [Lattice X] [TopologicalSpace X]
    (φ : X → ℝ) (hφc : Continuous φ) (hφm : StrictMono φ) {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K) :
    ∃ g ∈ K, ∀ y ∈ K, y ≤ g := by
  obtain ⟨g, hgK, hgmax⟩ := hK.exists_isMaxOn hne hφc.continuousOn
  refine ⟨g, hgK, fun y hy => ?_⟩
  have h1 : φ (y ⊔ g) ≤ φ g := isMaxOn_iff.1 hgmax _ (hsup y hy g hgK)
  by_contra hyg
  have hne' : g ≠ y ⊔ g := fun h => hyg (calc y ≤ y ⊔ g := le_sup_left
      _ = g := h.symm)
  have hlt : g < y ⊔ g := lt_of_le_of_ne le_sup_right hne'
  exact absurd (hφm hlt) (not_lt.mpr h1)

theorem exists_least_of_infClosed {X : Type*} [Lattice X] [TopologicalSpace X]
    (φ : X → ℝ) (hφc : Continuous φ) (hφm : StrictMono φ) {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hinf : ∀ a ∈ K, ∀ b ∈ K, a ⊓ b ∈ K) :
    ∃ g ∈ K, ∀ y ∈ K, g ≤ y := by
  obtain ⟨g, hgK, hgmin⟩ := hK.exists_isMinOn hne hφc.continuousOn
  refine ⟨g, hgK, fun y hy => ?_⟩
  have h1 : φ g ≤ φ (y ⊓ g) := isMinOn_iff.1 hgmin _ (hinf y hy g hgK)
  by_contra hyg
  have hne' : y ⊓ g ≠ g := fun h => hyg (calc g = y ⊓ g := h.symm
      _ ≤ y := inf_le_left)
  have hlt : y ⊓ g < g := lt_of_le_of_ne inf_le_right hne'
  exact absurd (hφm hlt) (not_lt.mpr h1)

theorem strictMono_sum_fin (n : ℕ) : StrictMono (fun y : Fin n → ℝ => ∑ j, y j) := by
  intro a b hab
  rw [Pi.lt_def] at hab
  obtain ⟨hle, j, hj⟩ := hab
  exact Finset.sum_lt_sum (fun k _ => hle k) ⟨j, Finset.mem_univ _, hj⟩

theorem continuous_sum_fin (n : ℕ) : Continuous (fun y : Fin n → ℝ => ∑ j, y j) :=
  continuous_finsetSum _ (fun j _ => continuous_apply j)

section Game

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}

theorem strictMono_sum_X : StrictMono (fun x : (∀ i, Fin (m i) → ℝ) => ∑ i, ∑ j, x i j) := by
  intro a b hab
  rw [Pi.lt_def] at hab
  obtain ⟨hle, i, hi⟩ := hab
  exact Finset.sum_lt_sum (fun k _ => Finset.sum_le_sum (fun j _ => hle k j))
    ⟨i, Finset.mem_univ _, strictMono_sum_fin (m i) hi⟩

theorem continuous_sum_X : Continuous (fun x : (∀ i, Fin (m i) → ℝ) => ∑ i, ∑ j, x i j) :=
  continuous_finsetSum _ (fun i _ => continuous_finsetSum _
    (fun j _ => (continuous_apply j).comp (continuous_apply i)))

theorem isCompact_section {S : Set (∀ i, Fin (m i) → ℝ)} (hS : IsCompact S)
    (x : ∀ i, Fin (m i) → ℝ) (i : ι) :
    IsCompact {y : Fin (m i) → ℝ | Function.update x i y ∈ S} := by
  have hcl : IsClosed {y : Fin (m i) → ℝ | Function.update x i y ∈ S} :=
    hS.isClosed.preimage (continuous_const.update i continuous_id)
  have hsub : {y : Fin (m i) → ℝ | Function.update x i y ∈ S} ⊆
      (fun z : (∀ i, Fin (m i) → ℝ) => z i) '' S := by
    intro y hy
    exact ⟨_, hy, by simp⟩
  exact (hS.image (continuous_apply i)).of_isClosed_subset hcl hsub

/-- best-response set -/
def BR (S : Set (∀ i, Fin (m i) → ℝ)) (F : ι → (∀ i, Fin (m i) → ℝ) → ℝ) (i : ι)
    (x : ∀ i, Fin (m i) → ℝ) : Set (Fin (m i) → ℝ) :=
  {y | Function.update x i y ∈ S ∧ ∀ z : Fin (m i) → ℝ, Function.update x i z ∈ S →
    F i (Function.update x i z) ≤ F i (Function.update x i y)}

theorem BR_props (S : Set (∀ i, Fin (m i) → ℝ)) (F : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hsub : IsSublattice S) (hS : IsCompact S)
    (hsm : ∀ i, ∀ x ∈ projOthers S i,
      SupermodularOn (fun y : Fin (m i) → ℝ => F i (Function.update x i y)) (proj S i))
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => F i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    (x : ∀ i, Fin (m i) → ℝ) (hx : x ∈ S) (i : ι) :
    (∃ y, IsGreatest (BR S F i x) y) ∧ (∃ y, IsLeast (BR S F i x) y) := by
  have hA := isCompact_section hS x i
  have hxi : x i ∈ {y : Fin (m i) → ℝ | Function.update x i y ∈ S} := by
    simp only [Set.mem_setOf_eq, Function.update_eq_self]; exact hx
  obtain ⟨y0, hy0A, hy0max⟩ := (husc i x).exists_isMaxOn ⟨x i, hxi⟩ hA
  have hBReq : BR S F i x = {y : Fin (m i) → ℝ | Function.update x i y ∈ S} ∩
      (fun y : Fin (m i) → ℝ => F i (Function.update x i y)) ⁻¹'
        Set.Ici (F i (Function.update x i y0)) := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 y0 hy0A⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z hz => (isMaxOn_iff.1 hy0max z hz).trans h2⟩
  obtain ⟨v, hv, heq⟩ := upperSemicontinuousOn_iff_preimage_Ici.1 (husc i x)
    (F i (Function.update x i y0))
  have hK : IsCompact (BR S F i x) := by
    rw [hBReq, heq]; exact hA.inter_right hv
  have hne : (BR S F i x).Nonempty :=
    ⟨y0, hy0A, fun z hz => isMaxOn_iff.1 hy0max z hz⟩
  have hxO : x ∈ projOthers S i := ⟨x i, by rw [Function.update_eq_self]; exact hx⟩
  have hsupinf : ∀ y ∈ BR S F i x, ∀ y' ∈ BR S F i x,
      y ⊔ y' ∈ BR S F i x ∧ y ⊓ y' ∈ BR S F i x := by
    intro y hy y' hy'
    have hfs : Function.update x i (y ⊔ y') ∈ S := by
      rw [Function.update_sup]; exact hsub.supClosed hy.1 hy'.1
    have hfi : Function.update x i (y ⊓ y') ∈ S := by
      rw [Function.update_inf]; exact hsub.infClosed hy.1 hy'.1
    have hsm' := hsm i x hxO (show y ∈ proj S i from ⟨x, hy.1⟩)
      (show y' ∈ proj S i from ⟨x, hy'.1⟩)
    simp only at hsm'
    have a1 := hy.2 _ hfs
    have a2 := hy.2 _ hfi
    have a3 := hy.2 _ hy'.1
    have a4 := hy'.2 _ hy.1
    refine ⟨⟨hfs, fun z hz => ?_⟩, ⟨hfi, fun z hz => ?_⟩⟩
    · have := hy.2 z hz; linarith
    · have := hy.2 z hz; linarith
  constructor
  · obtain ⟨g, hg, hgle⟩ := exists_greatest_of_supClosed _ (continuous_sum_fin (m i))
      (strictMono_sum_fin (m i)) hK hne (fun a ha b hb => (hsupinf a ha b hb).1)
    exact ⟨g, hg, hgle⟩
  · obtain ⟨g, hg, hgle⟩ := exists_least_of_infClosed _ (continuous_sum_fin (m i))
      (strictMono_sum_fin (m i)) hK hne (fun a ha b hb => (hsupinf a ha b hb).2)
    exact ⟨g, hg, hgle⟩

theorem abstract_greatest {S : Set (∀ i, Fin (m i) → ℝ)} (hS : IsCompact S)
    (hSne : S.Nonempty) (hsub : IsSublattice S)
    (M : ∀ i, (∀ i, Fin (m i) → ℝ) → Set (Fin (m i) → ℝ))
    (hfeas : ∀ x i y, y ∈ M i x → Function.update x i y ∈ S)
    (hgr : ∀ x ∈ S, ∀ i, ∃ y, IsGreatest (M i x) y)
    (hkey : ∀ x ∈ S, ∀ x' ∈ S, x ≤ x' → ∀ i, ∀ y ∈ M i x, ∀ y' ∈ M i x', y ⊔ y' ∈ M i x') :
    ∃ g ∈ S, (∀ i, g i ∈ M i g) ∧ ∀ x ∈ S, (∀ i, ∃ y ∈ M i x, x i ≤ y) → x ≤ g := by
  choose! G hG using hgr
  have hmono : ∀ x ∈ S, ∀ x' ∈ S, x ≤ x' → ∀ i, G x i ≤ G x' i := by
    intro x hx x' hx' hle i
    exact le_sup_left.trans ((hG x' hx' i).2 (hkey x hx x' hx' hle i _ (hG x hx i).1 _
      (hG x' hx' i).1))
  set U := {x ∈ S | ∀ i, x i ≤ G x i} with hU
  set B := {z ∈ S | ∀ u ∈ U, u ≤ z} with hB
  have hBc : IsCompact B := by
    have : B = S ∩ ⋂ u ∈ U, {z | u ≤ z} := by
      ext z; simp [hB]
    rw [this]
    exact hS.inter_right (isClosed_biInter fun u _ => isClosed_le continuous_const continuous_id)
  obtain ⟨top, htop, htople⟩ := exists_greatest_of_supClosed _ continuous_sum_X
    strictMono_sum_X hS hSne (fun a ha b hb => hsub.supClosed ha hb)
  have hBne : B.Nonempty := ⟨top, htop, fun u hu => htople u hu.1⟩
  obtain ⟨xs, hxsB, hxsle⟩ := exists_least_of_infClosed _ continuous_sum_X
    strictMono_sum_X hBc hBne
    (fun a ha b hb => ⟨hsub.infClosed ha.1 hb.1, fun u hu => le_inf (ha.2 u hu) (hb.2 u hu)⟩)
  have hxsS : xs ∈ S := hxsB.1
  have hwS : ∀ i, Function.update xs i (G xs i) ∈ S := fun i => hfeas _ _ _ (hG xs hxsS i).1
  have step1 : ∀ i, xs i ≤ G xs i := by
    intro i
    have hwB : Function.update xs i (G xs i) ∈ B := by
      refine ⟨hwS i, fun u hu => ?_⟩
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact (hu.2 j).trans (hmono u hu.1 xs hxsS (hxsB.2 u hu) j)
      · simp only [Function.update_of_ne hj]
        exact hxsB.2 u hu j
    have := hxsle _ hwB i
    simpa using this
  have hxsw : ∀ i, xs ≤ Function.update xs i (G xs i) := by
    intro i j
    by_cases hj : j = i
    · subst hj; simpa using step1 j
    · simp [Function.update_of_ne hj]
  have step2 : ∀ i, G xs i ≤ xs i := by
    intro i
    have hwU : Function.update xs i (G xs i) ∈ U := by
      refine ⟨hwS i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact hmono xs hxsS _ (hwS j) (hxsw j) j
      · simp only [Function.update_of_ne hj]
        exact (step1 j).trans (hmono xs hxsS _ (hwS i) (hxsw i) j)
    have := hxsB.2 _ hwU i
    simpa using this
  refine ⟨xs, hxsS, fun i => ?_, fun x hx hxy => ?_⟩
  · have h := (hG xs hxsS i).1
    rwa [le_antisymm (step2 i) (step1 i)] at h
  · refine hxsB.2 x ⟨hx, fun i => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hxy i
    exact hxy.trans ((hG x hx i).2 hy)

theorem abstract_least {S : Set (∀ i, Fin (m i) → ℝ)} (hS : IsCompact S)
    (hSne : S.Nonempty) (hsub : IsSublattice S)
    (M : ∀ i, (∀ i, Fin (m i) → ℝ) → Set (Fin (m i) → ℝ))
    (hfeas : ∀ x i y, y ∈ M i x → Function.update x i y ∈ S)
    (hle : ∀ x ∈ S, ∀ i, ∃ y, IsLeast (M i x) y)
    (hkey : ∀ x ∈ S, ∀ x' ∈ S, x ≤ x' → ∀ i, ∀ y ∈ M i x, ∀ y' ∈ M i x', y ⊓ y' ∈ M i x) :
    ∃ g ∈ S, (∀ i, g i ∈ M i g) ∧ ∀ x ∈ S, (∀ i, ∃ y ∈ M i x, y ≤ x i) → g ≤ x := by
  choose! G hG using hle
  have hmono : ∀ x ∈ S, ∀ x' ∈ S, x ≤ x' → ∀ i, G x i ≤ G x' i := by
    intro x hx x' hx' hle i
    exact ((hG x hx i).2 (hkey x hx x' hx' hle i _ (hG x hx i).1 _
      (hG x' hx' i).1)).trans inf_le_right
  set U := {x ∈ S | ∀ i, G x i ≤ x i} with hU
  set B := {z ∈ S | ∀ u ∈ U, z ≤ u} with hB
  have hBc : IsCompact B := by
    have : B = S ∩ ⋂ u ∈ U, {z | z ≤ u} := by
      ext z; simp [hB]
    rw [this]
    exact hS.inter_right (isClosed_biInter fun u _ => isClosed_le continuous_id continuous_const)
  obtain ⟨bot, hbot, hbotle⟩ := exists_least_of_infClosed _ continuous_sum_X
    strictMono_sum_X hS hSne (fun a ha b hb => hsub.infClosed ha hb)
  have hBne : B.Nonempty := ⟨bot, hbot, fun u hu => hbotle u hu.1⟩
  obtain ⟨xs, hxsB, hxsle⟩ := exists_greatest_of_supClosed _ continuous_sum_X
    strictMono_sum_X hBc hBne
    (fun a ha b hb => ⟨hsub.supClosed ha.1 hb.1, fun u hu => sup_le (ha.2 u hu) (hb.2 u hu)⟩)
  have hxsS : xs ∈ S := hxsB.1
  have hwS : ∀ i, Function.update xs i (G xs i) ∈ S := fun i => hfeas _ _ _ (hG xs hxsS i).1
  have step1 : ∀ i, G xs i ≤ xs i := by
    intro i
    have hwB : Function.update xs i (G xs i) ∈ B := by
      refine ⟨hwS i, fun u hu => ?_⟩
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact (hmono xs hxsS u hu.1 (hxsB.2 u hu) j).trans (hu.2 j)
      · simp only [Function.update_of_ne hj]
        exact hxsB.2 u hu j
    have := hxsle _ hwB i
    simpa using this
  have hxsw : ∀ i, Function.update xs i (G xs i) ≤ xs := by
    intro i j
    by_cases hj : j = i
    · subst hj; simpa using step1 j
    · simp [Function.update_of_ne hj]
  have step2 : ∀ i, xs i ≤ G xs i := by
    intro i
    have hwU : Function.update xs i (G xs i) ∈ U := by
      refine ⟨hwS i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact hmono _ (hwS j) xs hxsS (hxsw j) j
      · simp only [Function.update_of_ne hj]
        exact (hmono _ (hwS i) xs hxsS (hxsw i) j).trans (step1 j)
    have := hxsB.2 _ hwU i
    simpa using this
  refine ⟨xs, hxsS, fun i => ?_, fun x hx hxy => ?_⟩
  · have h := (hG xs hxsS i).1
    rwa [le_antisymm (step1 i) (step2 i)] at h
  · refine hxsB.2 x ⟨hx, fun i => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hxy i
    exact ((hG x hx i).2 hy).trans hxy

theorem update_inf_of_le (x x' : ∀ i, Fin (m i) → ℝ) (hle : x ≤ x') (i : ι)
    (y y' : Fin (m i) → ℝ) :
    Function.update x i (y ⊓ y') = Function.update x i y ⊓ Function.update x' i y' := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj, inf_eq_left.mpr (hle j)]

theorem update_sup_of_le (x x' : ∀ i, Fin (m i) → ℝ) (hle : x ≤ x') (i : ι)
    (y y' : Fin (m i) → ℝ) :
    Function.update x' i (y ⊔ y') = Function.update x i y ⊔ Function.update x' i y' := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj, sup_eq_right.mpr (hle j)]

end Game

end P801

open Supermodularity.Games in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {m : ι → ℕ} {T : Type*} [PartialOrder T]
    (S : T → Set (∀ i, Fin (m i) → ℝ)) (f : T → ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : ∀ t, IsSupermodularGame (S t) (f t))
    (hsuper_union : ∀ t i, ∀ x ∈ (⋃ s : T, projOthers (S s) i),
      Supermodularity.Monotonicity.SupermodularOn
        (fun y : Fin (m i) → ℝ => f t i (Function.update x i y)) (⋃ s : T, proj (S s) i))
    (hdiff_union : ∀ t i,
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (x : ∀ i, Fin (m i) → ℝ) => f t i (Function.update x i y))
        ((⋃ s : T, proj (S s) i) ×ˢ (⋃ s : T, projOthers (S s) i)))
    (hSne : ∀ t, (S t).Nonempty) (hScompact : ∀ t, IsCompact (S t))
    (hSinc : ∀ ⦃t t' : T⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (husc : ∀ t i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f t i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S t})
    (hdiff : ∀ i, ∀ x ∈ (⋃ t : T, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (t : T) => f t i (Function.update x i y))
        ((⋃ t : T, proj (S t) i) ×ˢ (Set.univ : Set T))) :
    ∃ g l : T → (∀ i, Fin (m i) → ℝ),
      (∀ t, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (g t)) ∧
      (∀ t, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (l t)) ∧
      Monotone g ∧ Monotone l := by
  -- key comparative-statics lemma
  have key : ∀ ⦃t t' : T⦄, t ≤ t' → ∀ x ∈ S t, ∀ x' ∈ S t', x ≤ x' → ∀ i,
      ∀ y ∈ P801.BR (S t) (f t) i x, ∀ y' ∈ P801.BR (S t') (f t') i x',
      y ⊓ y' ∈ P801.BR (S t) (f t) i x ∧ y ⊔ y' ∈ P801.BR (S t') (f t') i x' := by
    intro t t' htt x hx x' hx' hxx i y hy y' hy'
    have hfi : Function.update x i (y ⊓ y') ∈ S t := by
      rw [P801.update_inf_of_le x x' hxx]; exact ((hSinc htt) hy.1 hy'.1).1
    have hfs : Function.update x' i (y ⊔ y') ∈ S t' := by
      rw [P801.update_sup_of_le x x' hxx]; exact ((hSinc htt) hy.1 hy'.1).2
    have hyU : y ∈ ⋃ s : T, proj (S s) i := Set.mem_iUnion.2 ⟨t, x, hy.1⟩
    have hy'U : y' ∈ ⋃ s : T, proj (S s) i := Set.mem_iUnion.2 ⟨t', x', hy'.1⟩
    have hysU : y ⊔ y' ∈ ⋃ s : T, proj (S s) i := Set.mem_iUnion.2 ⟨t', x', hfs⟩
    have hxU : x ∈ ⋃ s : T, projOthers (S s) i :=
      Set.mem_iUnion.2 ⟨t, x i, by rw [Function.update_eq_self]; exact hx⟩
    have hx'U : x' ∈ ⋃ s : T, projOthers (S s) i :=
      Set.mem_iUnion.2 ⟨t', x' i, by rw [Function.update_eq_self]; exact hx'⟩
    have hsm : f t i (Function.update x i y) + f t i (Function.update x i y') ≤
        f t i (Function.update x i (y ⊔ y')) + f t i (Function.update x i (y ⊓ y')) :=
      hsuper_union t i x hxU hyU hy'U
    have hidx : f t i (Function.update x' i y') - f t i (Function.update x i y') ≤
        f t i (Function.update x' i (y ⊔ y')) - f t i (Function.update x i (y ⊔ y')) := by
      rcases eq_or_lt_of_le hxx with h | h
      · subst h; simp
      · exact hdiff_union t i h ⟨⟨hy'U, hxU⟩, ⟨hy'U, hx'U⟩⟩ ⟨⟨hysU, hxU⟩, ⟨hysU, hx'U⟩⟩
          le_sup_right
    have hidt : f t' i (Function.update x' i y') - f t i (Function.update x' i y') ≤
        f t' i (Function.update x' i (y ⊔ y')) - f t i (Function.update x' i (y ⊔ y')) := by
      rcases eq_or_lt_of_le htt with h | h
      · subst h; simp
      · exact hdiff i x' hx'U h ⟨⟨hy'U, Set.mem_univ _⟩, ⟨hy'U, Set.mem_univ _⟩⟩
          ⟨⟨hysU, Set.mem_univ _⟩, ⟨hysU, Set.mem_univ _⟩⟩ le_sup_right
    have ha := hy.2 _ hfi
    have hb := hy'.2 _ hfs
    refine ⟨⟨hfi, fun z hz => ?_⟩, ⟨hfs, fun z hz => ?_⟩⟩
    · have := hy.2 z hz; linarith
    · have := hy'.2 z hz; linarith
  have hBR : ∀ t, ∀ x ∈ S t, ∀ i, (∃ y, IsGreatest (P801.BR (S t) (f t) i x) y) ∧
      (∃ y, IsLeast (P801.BR (S t) (f t) i x) y) := fun t x hx i =>
    P801.BR_props (S t) (f t) (hgame t).sublattice (hScompact t) (hgame t).supermodular
      (husc t) x hx i
  have hfeas : ∀ t x i y, y ∈ P801.BR (S t) (f t) i x → Function.update x i y ∈ S t :=
    fun t x i y hy => hy.1
  have hG : ∀ t, ∃ g ∈ S t, (∀ i, g i ∈ P801.BR (S t) (f t) i g) ∧
      ∀ x ∈ S t, (∀ i, ∃ y ∈ P801.BR (S t) (f t) i x, x i ≤ y) → x ≤ g := fun t =>
    P801.abstract_greatest (hScompact t) (hSne t) (hgame t).sublattice (fun i x => P801.BR (S t) (f t) i x)
      (hfeas t) (fun x hx i => (hBR t x hx i).1)
      (fun x hx x' hx' hle i y hy y' hy' => (key le_rfl x hx x' hx' hle i y hy y' hy').2)
  have hL : ∀ t, ∃ g ∈ S t, (∀ i, g i ∈ P801.BR (S t) (f t) i g) ∧
      ∀ x ∈ S t, (∀ i, ∃ y ∈ P801.BR (S t) (f t) i x, y ≤ x i) → g ≤ x := fun t =>
    P801.abstract_least (hScompact t) (hSne t) (hgame t).sublattice (fun i x => P801.BR (S t) (f t) i x)
      (hfeas t) (fun x hx i => (hBR t x hx i).2)
      (fun x hx x' hx' hle i y hy y' hy' => (key le_rfl x hx x' hx' hle i y hy y' hy').1)
  choose g hgS hgfix hgmax using hG
  choose l hlS hlfix hlmin using hL
  have hEq : ∀ t e, IsEquilibrium (S t) (f t) e ↔ e ∈ S t ∧ ∀ i, e i ∈ P801.BR (S t) (f t) i e := by
    intro t e
    constructor
    · rintro ⟨he, hi⟩
      refine ⟨he, fun i => ⟨by rw [Function.update_eq_self]; exact he, fun z hz => ?_⟩⟩
      rw [Function.update_eq_self]; exact hi i z hz
    · rintro ⟨he, hi⟩
      refine ⟨he, fun i y hy => ?_⟩
      have := (hi i).2 y hy
      rwa [Function.update_eq_self] at this
  refine ⟨g, l, fun t => ⟨(hEq t (g t)).2 ⟨hgS t, hgfix t⟩, fun e he => ?_⟩,
    fun t => ⟨(hEq t (l t)).2 ⟨hlS t, hlfix t⟩, fun e he => ?_⟩, ?_, ?_⟩
  · obtain ⟨heS, hei⟩ := (hEq t e).1 he
    exact hgmax t e heS (fun i => ⟨e i, hei i, le_rfl⟩)
  · obtain ⟨heS, hei⟩ := (hEq t e).1 he
    exact hlmin t e heS (fun i => ⟨e i, hei i, le_rfl⟩)
  · intro t t' htt
    have hv : g t ⊔ g t' ∈ S t' := ((hSinc htt) (hgS t) (hgS t')).2
    have hvle : g t ⊔ g t' ≤ g t' := by
      refine hgmax t' _ hv (fun i => ?_)
      obtain ⟨y0, hy0, -⟩ := (hBR t' _ hv i).1
      have h1 := (key htt (g t) (hgS t) _ hv le_sup_left i _ (hgfix t i) y0 hy0).2
      have h2 := (key le_rfl (g t') (hgS t') _ hv le_sup_right i _ (hgfix t' i) _ h1).2
      refine ⟨_, h2, ?_⟩
      simp only [Pi.sup_apply]
      exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
    exact le_sup_left.trans hvle
  · intro t t' htt
    have hv : l t ⊓ l t' ∈ S t := ((hSinc htt) (hlS t) (hlS t')).1
    have hvle : l t ≤ l t ⊓ l t' := by
      refine hlmin t _ hv (fun i => ?_)
      obtain ⟨y0, hy0, -⟩ := (hBR t _ hv i).2
      have h1 := (key htt _ hv (l t') (hlS t') inf_le_right i y0 hy0 _ (hlfix t' i)).1
      have h2 := (key le_rfl _ hv (l t) (hlS t) inf_le_left i _ h1 _ (hlfix t i)).1
      refine ⟨_, h2, ?_⟩
      simp only [Pi.inf_apply]
      exact le_inf (inf_le_right) (inf_le_left.trans inf_le_right)
    exact hvle.trans inf_le_right
