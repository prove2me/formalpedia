-- Prove2me | solution 1 for OpenPitMIP.UltPit.upit_unique_minimal_optimal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:32:02.243965+00:00
-- url     : https://prove2.me/submissions/94691361-c021-4a96-9859-e60b75819b04

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

set_option autoImplicit false
open OpenPitMIP.UltPit PCPSPC

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [Nonempty D] {T m : ℕ} (I : PCPSPC B D C T m) :
    ∃! x : C → ℝ, I.UPitMinimalOptimal x := by
  classical
  let F : Set (C → ℝ) := {x | I.UPitFeasible x}
  have hobjc : Continuous (fun x : C → ℝ => I.UPitObjective x) := by
    unfold PCPSPC.UPitObjective
    exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_apply c)
  have hFclosed : IsClosed F := by
    have : F = (⋂ c, ⋂ c', ⋂ (_ : I.arc c c'), {x : C → ℝ | x c ≤ x c'}) ∩
        (⋂ c, {x : C → ℝ | 0 ≤ x c} ∩ {x | x c ≤ 1}) := by
      ext x
      simp [F, UPitFeasible, forall_and]
    rw [this]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply c) (continuous_apply c')
    · exact isClosed_iInter fun c => IsClosed.inter
        (isClosed_le continuous_const (continuous_apply c))
        (isClosed_le (continuous_apply c) continuous_const)
  have hbox : F ⊆ Set.pi Set.univ (fun _ : C => Set.Icc (0:ℝ) 1) := by
    intro x hx c _
    exact hx.2 c
  have hFcomp : IsCompact F :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hFclosed hbox
  have hF0 : (0 : C → ℝ) ∈ F := ⟨fun c c' _ => le_refl _, fun c => ⟨le_refl _, zero_le_one⟩⟩
  obtain ⟨x0, hx0F, hx0max⟩ := hFcomp.exists_isMaxOn ⟨0, hF0⟩ hobjc.continuousOn
  have hx0 : ∀ x ∈ F, I.UPitObjective x ≤ I.UPitObjective x0 := fun x hx => hx0max hx
  -- optimal set
  let O : Set (C → ℝ) := F ∩ {x | I.UPitObjective x0 ≤ I.UPitObjective x}
  have hOpt : ∀ x, I.UPitOptimal x ↔ x ∈ O := by
    intro x
    constructor
    · intro h
      exact ⟨h.1, h.2 x0 hx0F⟩
    · intro h
      exact ⟨h.1, fun x' hx' => (hx0 x' hx').trans h.2⟩
  have hOcomp : IsCompact O :=
    hFcomp.inter_right (isClosed_le continuous_const hobjc)
  have hx0O : x0 ∈ O := ⟨hx0F, show I.UPitObjective x0 ≤ I.UPitObjective x0 from le_rfl⟩
  have hsc : Continuous (fun x : C → ℝ => ∑ c, x c) :=
    continuous_finsetSum _ fun c _ => continuous_apply c
  obtain ⟨xh, hxhO, hxhmin⟩ := hOcomp.exists_isMinOn ⟨x0, hx0O⟩ hsc.continuousOn
  have hxh : ∀ x ∈ O, ∑ c, xh c ≤ ∑ c, x c := fun x hx => hxhmin hx
  -- lattice
  have hmin : ∀ x x' : C → ℝ, x ∈ F → x' ∈ F → (fun c => min (x c) (x' c)) ∈ F := by
    intro x x' hx hx'
    exact ⟨fun c c' h => min_le_min (hx.1 c c' h) (hx'.1 c c' h),
      fun c => ⟨le_min (hx.2 c).1 (hx'.2 c).1, (min_le_left _ _).trans (hx.2 c).2⟩⟩
  have hmax : ∀ x x' : C → ℝ, x ∈ F → x' ∈ F → (fun c => max (x c) (x' c)) ∈ F := by
    intro x x' hx hx'
    exact ⟨fun c c' h => max_le_max (hx.1 c c' h) (hx'.1 c c' h),
      fun c => ⟨(hx.2 c).1.trans (le_max_left _ _), max_le (hx.2 c).2 (hx'.2 c).2⟩⟩
  have hobjsum : ∀ x x' : C → ℝ, I.UPitObjective (fun c => min (x c) (x' c)) +
      I.UPitObjective (fun c => max (x c) (x' c)) = I.UPitObjective x + I.UPitObjective x' := by
    intro x x'
    unfold PCPSPC.UPitObjective
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_add, ← mul_add, min_add_max]
  have hleast : ∀ x' : C → ℝ, I.UPitOptimal x' → xh ≤ x' := by
    intro x' hx'
    have hx'O := (hOpt x').1 hx'
    have hm := hmin xh x' hxhO.1 hx'O.1
    have hM := hmax xh x' hxhO.1 hx'O.1
    have hs := hobjsum xh x'
    have h1 := hx0 _ hm
    have h2 := hx0 _ hM
    have h3 : I.UPitObjective x0 ≤ I.UPitObjective xh := hxhO.2
    have h4 : I.UPitObjective x0 ≤ I.UPitObjective x' := hx'O.2
    have hmO : (fun c => min (xh c) (x' c)) ∈ O := by
      refine ⟨hm, ?_⟩
      show I.UPitObjective x0 ≤ _
      linarith
    have hle : ∑ c, xh c ≤ ∑ c, min (xh c) (x' c) := hxh _ hmO
    have hz : ∑ c, (xh c - min (xh c) (x' c)) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg fun c _ => sub_nonneg.2 (min_le_left _ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sub_nonneg.2 (min_le_left _ _))] at hz
    intro c
    have := hz c (Finset.mem_univ c)
    have : min (xh c) (x' c) = xh c := by linarith
    exact min_eq_left_iff.1 this
  refine ⟨xh, ⟨(hOpt xh).2 hxhO, fun x' hx' hle => le_antisymm hle (hleast x' hx')⟩, ?_⟩
  intro y hy
  exact (hy.2 xh ((hOpt xh).2 hxhO) (hleast y hy.1)).symm
