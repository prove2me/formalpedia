-- Prove2me | solution 1 for ThompsonAmenability.not_isLiouville_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:51:55.593262+00:00
-- url     : https://prove2.me/submissions/56fae890-fde3-4ac6-9ec8-7780266307ce

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_bijOn_dyadic
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F
import Theorems.Thm_ThompsonWalk_summable_green_of_isStrictlyNondegenerate

section
section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-!
# Blueprint: Kaimanovich — Thompson's group F is not Liouville

For a finitely supported, strictly non-degenerate probability `μ` on `F`, we build a bounded
non-constant `μ`-harmonic function on `F`, analytically (convolution powers only, no path space):
* the slope-jump cocycle `jump g t` (log₂ of right slope over left slope of `g` at `t`) satisfies
  `jump (g * h) t = jump h t + jump g (h t)`; the transported configuration
  `cfg g y = jump g (g⁻¹ y)` satisfies `cfg (g * h) y = cfg g y + cfg h (g⁻¹ y)`;
* transience (part T): from any dyadic `y ∈ (0,1)` the walk `y ↦ g⁻¹ y`, `g ∼ μ^{*n}`, visits a finite
  set only summably often (Kaimanovich, Theorems 14, 16, 25);
* hence the law of `cfg (g * h) (1/2)` under `h ∼ μ^{*n}` converges as `n → ∞` (its changes are bounded
  by visits to a finite set), to a probability law `p g` on `ℤ`, harmonic in `g`;
* an element `b` fixing `1/2` with `jump b (1/2) = d ≠ 0` shifts the law by `d`; Liouville would make
  `p g` independent of `g`, so `p 1` would be `d`-periodic and summable to `1`: impossible.
-/
/-- Thompson's group `F` as a type. -/
abbrev FF := ↥CannonFloydParry.F

/-- The action of `g ∈ F` on `ℝ` (by the identity off `[0,1]`). -/
noncomputable def act (g : FF) (t : ℝ) : ℝ := CannonFloydParry.extend (g : UI ≃o UI) t

/-- Convolution of finitely supported functions on `F`: `(ν ⋆ μ)(x) = ∑_{gh = x} ν g · μ h`. -/
noncomputable def conv (ν μ : FF →₀ ℝ) : FF →₀ ℝ :=
  ν.sum fun g a => μ.sum fun h b => Finsupp.single (g * h) (a * b)

/-- Convolution powers: `cpow μ n` is the law of `g₁ ⋯ gₙ` for independent `gᵢ ∼ μ`. -/
noncomputable def cpow (μ : FF →₀ ℝ) : ℕ → (FF →₀ ℝ)
  | 0 => Finsupp.single 1 1
  | n + 1 => conv (cpow μ n) μ

/-- The probability that the walk from `y` is in `A` after `n` steps. -/
noncomputable def hit (μ : FF →₀ ℝ) (n : ℕ) (y : ℝ) (A : Finset ℝ) : ℝ :=
  (cpow μ n).sum fun g w => if act g⁻¹ y ∈ A then w else 0

/-- The jump of `log₂` of the slope of `g` at `t`: right slope over left slope. -/
noncomputable def jump (g : FF) (t : ℝ) : ℤ :=
  Int.log 2 (derivWithin (act g) (Set.Ici t) t) - Int.log 2 (derivWithin (act g) (Set.Iic t) t)

/-- The configuration of `g`, transported to the image points. -/
noncomputable def cfg (g : FF) (y : ℝ) : ℤ := jump g (act g⁻¹ y)

/-- The law of the configuration at `1/2` of `g * h`, `h ∼ μ^{*n}`. -/
noncomputable def pdist (μ : FF →₀ ℝ) (n : ℕ) (g : FF) (k : ℤ) : ℝ :=
  (cpow μ n).sum fun h w => if cfg (g * h) (1 / 2) = k then w else 0

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
/-!
# Part C: the action of `F` on the line and the slope-jump cocycle

* `act_mul`, `act_one`: `act` is an action (multiplication in `F` is composition).
* `act_dyadic`: `F` preserves the dyadic points of `(0,1)`.
* `jump_mul`: near any point an element of `F` is affine with a power-of-two slope on each side;
  composing the one-sided affine pieces gives the cocycle identity.
* `finite_jump`: off the breakpoints (and `0`, `1`) the two one-sided slopes agree.
* `exists_jump_half`: `mapB` fixes `1/2`, with slope `1` on the left and `1/2` on the right.
-/
/-! ### `extend` -/
lemma extend_of_mem' (f : UI ≃o UI) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    extend f z = (f ⟨z, hz⟩ : ℝ) := by
  rw [extend_apply, extendFun_of_mem f hz]

lemma apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  have h : f ⟨0, zero_mem_UI⟩ ≤ f (f.symm ⟨0, zero_mem_UI⟩) :=
    f.monotone (show (⟨0, zero_mem_UI⟩ : UI) ≤ f.symm ⟨0, zero_mem_UI⟩ from
      (f.symm ⟨0, zero_mem_UI⟩).2.1)
  rw [f.apply_symm_apply] at h
  exact le_antisymm h (f ⟨0, zero_mem_UI⟩).2.1

lemma apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  have h : f (f.symm ⟨1, one_mem_UI⟩) ≤ f ⟨1, one_mem_UI⟩ :=
    f.monotone (show f.symm ⟨1, one_mem_UI⟩ ≤ (⟨1, one_mem_UI⟩ : UI) from
      (f.symm ⟨1, one_mem_UI⟩).2.2)
  rw [f.apply_symm_apply] at h
  exact le_antisymm (f ⟨1, one_mem_UI⟩).2.2 h

lemma extend_of_nonpos (f : UI ≃o UI) {z : ℝ} (hz : z ≤ 0) : extend f z = z := by
  rcases hz.lt_or_eq with hz | rfl
  · rw [extend_apply, extendFun_of_notMem f (fun h => absurd h.1 (not_le.mpr hz))]
  · rw [extend_of_mem' f zero_mem_UI, apply_zero]

lemma extend_of_one_le (f : UI ≃o UI) {z : ℝ} (hz : 1 ≤ z) : extend f z = z := by
  rcases hz.lt_or_eq with hz | rfl
  · rw [extend_apply, extendFun_of_notMem f (fun h => absurd h.2 (not_le.mpr hz))]
  · rw [extend_of_mem' f one_mem_UI, apply_one]

lemma act_of_mem (g : FF) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    act g z = ((g : UI ≃o UI) ⟨z, hz⟩ : ℝ) :=
  extend_of_mem' _ hz

lemma act_of_nonpos (g : FF) {z : ℝ} (hz : z ≤ 0) : act g z = z := extend_of_nonpos _ hz

lemma act_of_one_le (g : FF) {z : ℝ} (hz : 1 ≤ z) : act g z = z := extend_of_one_le _ hz

lemma act_of_notMem (g : FF) {z : ℝ} (hz : z ∉ Set.Icc (0:ℝ) 1) : act g z = z := by
  unfold act
  rw [extend_apply, extendFun_of_notMem _ hz]

lemma act_mul' (g h : FF) (t : ℝ) : act (g * h) t = act g (act h t) := by
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · rw [act_of_mem _ ht, act_of_mem _ ht, act_of_mem _ (((h : UI ≃o UI) ⟨t, ht⟩).2)]
    rfl
  · rw [act_of_notMem _ ht, act_of_notMem _ ht, act_of_notMem _ ht]

lemma act_one' (t : ℝ) : act 1 t = t := by
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · rw [act_of_mem _ ht]
    rfl
  · rw [act_of_notMem _ ht]

theorem act_mul (g h : FF) (t : ℝ) : act (g * h) t = act g (act h t) := act_mul' g h t

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part C: the action and the cocycle -/
alias act_mul := ThompsonAmenability.Kai.PartC.act_mul

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
theorem act_one (t : ℝ) : act 1 t = t := act_one' t

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias act_one := ThompsonAmenability.Kai.PartC.act_one

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
theorem act_dyadic (g : FF) {y : ℝ} (hy : 0 < y ∧ y < 1 ∧ IsDyadic y) :
    0 < act g y ∧ act g y < 1 ∧ IsDyadic (act g y) := by
  obtain ⟨hy0, hy1, hyd⟩ := hy
  have hyI : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy0.le, hy1.le⟩
  rw [act_of_mem g hyI]
  set f : UI ≃o UI := (g : UI ≃o UI)
  refine ⟨?_, ?_, (bijOn_dyadic g.2).mapsTo hyd⟩
  · have h : f ⟨0, zero_mem_UI⟩ < f ⟨y, hyI⟩ :=
      f.strictMono (show (⟨0, zero_mem_UI⟩ : UI) < ⟨y, hyI⟩ from hy0)
    have h' : ((f ⟨0, zero_mem_UI⟩ : UI) : ℝ) < (f ⟨y, hyI⟩ : ℝ) := h
    rwa [apply_zero] at h'
  · have h : f ⟨y, hyI⟩ < f ⟨1, one_mem_UI⟩ :=
      f.strictMono (show (⟨y, hyI⟩ : UI) < ⟨1, one_mem_UI⟩ from hy1)
    have h' : ((f ⟨y, hyI⟩ : UI) : ℝ) < (f ⟨1, one_mem_UI⟩ : ℝ) := h
    rwa [apply_one] at h'

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias act_dyadic := ThompsonAmenability.Kai.PartC.act_dyadic

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
/-! ### One-sided slopes of affine germs -/
lemma log_derivWithin_Ici {f : ℝ → ℝ} {t b : ℝ} (htb : t < b) {n : ℤ} {c : ℝ}
    (h : ∀ z ∈ Set.Icc t b, f z = 2 ^ n * z + c) :
    Int.log 2 (derivWithin f (Set.Ici t) t) = n := by
  have hd : HasDerivWithinAt (fun z : ℝ => (2:ℝ) ^ n * z + c) (2 ^ n) (Set.Ici t) t := by
    simpa using (((hasDerivAt_id t).const_mul ((2:ℝ) ^ n)).add_const c).hasDerivWithinAt
  have hev : f =ᶠ[𝓝[Set.Ici t] t] (fun z : ℝ => (2:ℝ) ^ n * z + c) :=
    Filter.mem_of_superset (Icc_mem_nhdsGE htb) (fun z hz => h z hz)
  rw [(hd.congr_of_eventuallyEq hev (h t ⟨le_rfl, htb.le⟩)).derivWithin
    (uniqueDiffWithinAt_Ici t)]
  exact_mod_cast Int.log_zpow (R := ℝ) (b := 2) (by norm_num) n

lemma log_derivWithin_Iic {f : ℝ → ℝ} {a t : ℝ} (hat : a < t) {n : ℤ} {c : ℝ}
    (h : ∀ z ∈ Set.Icc a t, f z = 2 ^ n * z + c) :
    Int.log 2 (derivWithin f (Set.Iic t) t) = n := by
  have hd : HasDerivWithinAt (fun z : ℝ => (2:ℝ) ^ n * z + c) (2 ^ n) (Set.Iic t) t := by
    simpa using (((hasDerivAt_id t).const_mul ((2:ℝ) ^ n)).add_const c).hasDerivWithinAt
  have hev : f =ᶠ[𝓝[Set.Iic t] t] (fun z : ℝ => (2:ℝ) ^ n * z + c) :=
    Filter.mem_of_superset (Icc_mem_nhdsLE hat) (fun z hz => h z hz)
  rw [(hd.congr_of_eventuallyEq hev (h t ⟨hat.le, le_rfl⟩)).derivWithin
    (uniqueDiffWithinAt_Iic t)]
  exact_mod_cast Int.log_zpow (R := ℝ) (b := 2) (by norm_num) n

/-! ### Local affine structure of elements of `F` -/
/-- A finite set misses a punctured neighbourhood of every point. -/
lemma exists_punctured_gap (B : Finset ℝ) (t : ℝ) :
    ∃ ε > 0, ∀ z : ℝ, z ≠ t → |z - t| < ε → z ∉ B := by
  have hc : IsOpen ((B.erase t : Set ℝ)ᶜ) := (B.erase t).finite_toSet.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc t (by simp)
  refine ⟨ε, hε, fun z hzt hz hzB => ?_⟩
  have hzb : z ∈ Metric.ball t ε := by rw [Metric.mem_ball, Real.dist_eq]; exact hz
  exact hball hzb (by simp [hzt, hzB])

lemma gap_of_punctured {B : Finset ℝ} {t ε : ℝ} (hgap : ∀ z : ℝ, z ≠ t → |z - t| < ε → z ∉ B)
    {x y : ℝ} (hx : t - ε < x) (hy : y < t + ε) (ht : t ∉ Set.Ioo x y ∨ t ∉ B) :
    Set.Ioo x y ∩ (B : Set ℝ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨hz1, hz2⟩, hzB⟩
  by_cases hzt : z = t
  · subst hzt
    rcases ht with ht | ht
    · exact ht ⟨hz1, hz2⟩
    · exact ht hzB
  · exact hgap z hzt (by rw [abs_lt]; constructor <;> linarith) hzB

/-- On a right neighbourhood of every point, an element of `F` is affine with slope a power of
two. -/
lemma right_aff (g : FF) (t : ℝ) :
    ∃ b, t < b ∧ ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc t b, act g z = 2 ^ n * z + c := by
  rcases lt_or_ge t 0 with ht0 | ht0
  · refine ⟨0, ht0, 0, 0, fun z hz => ?_⟩
    rw [act_of_nonpos g hz.2]; simp
  rcases lt_or_ge t 1 with ht1 | ht1
  · obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp g.2
    obtain ⟨ε, hε, hgap⟩ := exists_punctured_gap B t
    set b := min (t + ε / 2) 1 with hb_def
    have hbε : b ≤ t + ε / 2 := min_le_left _ _
    have htb : t < b := lt_min (by linarith) ht1
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0, ht1.le⟩
    have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, min_le_right _ _⟩
    have hgap' : Set.Ioo ((⟨t, htI⟩ : UI) : ℝ) ((⟨b, hbI⟩ : UI) : ℝ) ∩ (B : Set ℝ) = ∅ :=
      gap_of_punctured hgap (show t - ε < t by linarith) (show b < t + ε by linarith)
        (Or.inl fun h => lt_irrefl t h.1)
    obtain ⟨n, c, hnc⟩ := hB ⟨t, htI⟩ ⟨b, hbI⟩ htb hgap'
    refine ⟨b, htb, n, c, fun z hz => ?_⟩
    have hzI : z ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz.1], le_trans hz.2 hbI.2⟩
    rw [act_of_mem g hzI]
    exact hnc ⟨z, hzI⟩ hz
  · refine ⟨t + 1, by linarith, 0, 0, fun z hz => ?_⟩
    rw [act_of_one_le g (le_trans ht1 hz.1)]; simp

/-- On a left neighbourhood of every point, an element of `F` is affine with slope a power of
two. -/
lemma left_aff (g : FF) (t : ℝ) :
    ∃ a, a < t ∧ ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc a t, act g z = 2 ^ n * z + c := by
  rcases lt_or_ge 1 t with ht1 | ht1
  · refine ⟨1, ht1, 0, 0, fun z hz => ?_⟩
    rw [act_of_one_le g hz.1]; simp
  rcases lt_or_ge 0 t with ht0 | ht0
  · obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp g.2
    obtain ⟨ε, hε, hgap⟩ := exists_punctured_gap B t
    set a := max (t - ε / 2) 0 with ha_def
    have haε : t - ε / 2 ≤ a := le_max_left _ _
    have hat : a < t := max_lt (by linarith) ht0
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1⟩
    have haI : a ∈ Set.Icc (0:ℝ) 1 := ⟨le_max_right _ _, by linarith⟩
    have hgap' : Set.Ioo ((⟨a, haI⟩ : UI) : ℝ) ((⟨t, htI⟩ : UI) : ℝ) ∩ (B : Set ℝ) = ∅ :=
      gap_of_punctured hgap (show t - ε < a by linarith) (show t < t + ε by linarith)
        (Or.inl fun h => lt_irrefl t h.2)
    obtain ⟨n, c, hnc⟩ := hB ⟨a, haI⟩ ⟨t, htI⟩ hat hgap'
    refine ⟨a, hat, n, c, fun z hz => ?_⟩
    have hzI : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans haI.1 hz.1, by linarith [hz.2]⟩
    rw [act_of_mem g hzI]
    exact hnc ⟨z, hzI⟩ hz
  · refine ⟨t - 1, by linarith, 0, 0, fun z hz => ?_⟩
    rw [act_of_nonpos g (le_trans hz.2 ht0)]; simp

/-- An element of `F` that is affine on a two-sided neighbourhood of `t` has no jump at `t`. -/
lemma jump_eq_zero_of_aff {g : FF} {a t b : ℝ} (hat : a < t) (htb : t < b) {n : ℤ} {c : ℝ}
    (h : ∀ z ∈ Set.Icc a b, act g z = 2 ^ n * z + c) : jump g t = 0 := by
  unfold jump
  rw [log_derivWithin_Ici htb (fun z hz => h z ⟨by linarith [hz.1], hz.2⟩),
    log_derivWithin_Iic hat (fun z hz => h z ⟨hz.1, by linarith [hz.2]⟩), sub_self]

/-! ### The cocycle -/
theorem jump_mul (g h : FF) (t : ℝ) : jump (g * h) t = jump h t + jump g (act h t) := by
  obtain ⟨b, htb, n, c, hh⟩ := right_aff h t
  obtain ⟨a, hat, n', c', hh'⟩ := left_aff h t
  set s := act h t with hs_def
  obtain ⟨b₁, hsb, m, d, hg⟩ := right_aff g s
  obtain ⟨a₁, has, m', d', hg'⟩ := left_aff g s
  have hp : (0:ℝ) < 2 ^ n := zpow_pos two_pos n
  have hp' : (0:ℝ) < 2 ^ n' := zpow_pos two_pos n'
  have hs : s = 2 ^ n * t + c := hh t ⟨le_rfl, htb.le⟩
  have hs' : s = 2 ^ n' * t + c' := hh' t ⟨hat.le, le_rfl⟩
  -- right of `t`
  set β := min b (t + (b₁ - s) / 2 ^ n) with hβ_def
  have hβ : t < β := lt_min htb (by have := div_pos (sub_pos.mpr hsb) hp; linarith)
  have hR : ∀ z ∈ Set.Icc t β, act (g * h) z = 2 ^ (m + n) * z + (2 ^ m * c + d) := by
    intro z hz
    have hzb : z ≤ b := le_trans hz.2 (min_le_left _ _)
    have hzb₁ : z - t ≤ (b₁ - s) / 2 ^ n := by linarith [le_trans hz.2 (min_le_right _ _)]
    rw [le_div_iff₀ hp] at hzb₁
    rw [act_mul', hh z ⟨hz.1, hzb⟩]
    have h1 : 2 ^ n * t ≤ 2 ^ n * z := mul_le_mul_of_nonneg_left hz.1 hp.le
    have hmem : 2 ^ n * z + c ∈ Set.Icc s b₁ := ⟨by linarith, by nlinarith⟩
    rw [hg _ hmem, zpow_add₀ two_ne_zero]
    ring
  -- left of `t`
  set α := max a (t - (s - a₁) / 2 ^ n') with hα_def
  have hα : α < t := max_lt hat (by have := div_pos (sub_pos.mpr has) hp'; linarith)
  have hL : ∀ z ∈ Set.Icc α t, act (g * h) z = 2 ^ (m' + n') * z + (2 ^ m' * c' + d') := by
    intro z hz
    have hza : a ≤ z := le_trans (le_max_left _ _) hz.1
    have hza₁ : t - z ≤ (s - a₁) / 2 ^ n' := by linarith [le_trans (le_max_right _ _) hz.1]
    rw [le_div_iff₀ hp'] at hza₁
    rw [act_mul', hh' z ⟨hza, hz.2⟩]
    have h1 : 2 ^ n' * z ≤ 2 ^ n' * t := mul_le_mul_of_nonneg_left hz.2 hp'.le
    have hmem : 2 ^ n' * z + c' ∈ Set.Icc a₁ s := ⟨by nlinarith, by linarith⟩
    rw [hg' _ hmem, zpow_add₀ two_ne_zero]
    ring
  unfold jump
  rw [log_derivWithin_Ici hβ hR, log_derivWithin_Iic hα hL, log_derivWithin_Ici htb hh,
    log_derivWithin_Iic hat hh', log_derivWithin_Ici hsb hg, log_derivWithin_Iic has hg']
  ring

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias jump_mul := ThompsonAmenability.Kai.PartC.jump_mul

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
theorem finite_jump (g : FF) : {t : ℝ | jump g t ≠ 0}.Finite := by
  classical
  obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp g.2
  refine (insert 0 (insert 1 B)).finite_toSet.subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq] at ht
  by_contra hmem
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hmem
  obtain ⟨ht0, ht1, htB⟩ := hmem
  apply ht
  rcases lt_or_gt_of_ne ht0 with ht0 | ht0
  · refine jump_eq_zero_of_aff (a := t - 1) (b := 0) (n := 0) (c := 0) (by linarith) ht0
      fun z hz => ?_
    rw [act_of_nonpos g hz.2]; simp
  rcases lt_or_gt_of_ne ht1 with ht1 | ht1
  · obtain ⟨ε, hε, hgap⟩ := exists_punctured_gap B t
    set a := max (t - ε / 2) 0 with ha_def
    set b := min (t + ε / 2) 1 with hb_def
    have haε : t - ε / 2 ≤ a := le_max_left _ _
    have hbε : b ≤ t + ε / 2 := min_le_left _ _
    have hat : a < t := max_lt (by linarith) ht0
    have htb : t < b := lt_min (by linarith) ht1
    have haI : a ∈ Set.Icc (0:ℝ) 1 := ⟨le_max_right _ _, by linarith⟩
    have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, min_le_right _ _⟩
    have hgap' : Set.Ioo ((⟨a, haI⟩ : UI) : ℝ) ((⟨b, hbI⟩ : UI) : ℝ) ∩ (B : Set ℝ) = ∅ :=
      gap_of_punctured hgap (show t - ε < a by linarith) (show b < t + ε by linarith)
        (Or.inr htB)
    obtain ⟨n, c, hnc⟩ := hB ⟨a, haI⟩ ⟨b, hbI⟩ (by show a < b; linarith) hgap'
    refine jump_eq_zero_of_aff hat htb (n := n) (c := c) fun z hz => ?_
    have hzI : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans haI.1 hz.1, le_trans hz.2 hbI.2⟩
    rw [act_of_mem g hzI]
    exact hnc ⟨z, hzI⟩ hz
  · refine jump_eq_zero_of_aff (a := 1) (b := t + 1) (n := 0) (c := 0) ht1 (by linarith)
      fun z hz => ?_
    rw [act_of_one_le g hz.1]; simp

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias finite_jump := ThompsonAmenability.Kai.PartC.finite_jump

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
/-! ### The element `B` -/
lemma mapB_mem_F : mapB ∈ F := by
  rw [← closure_mapA_mapB_eq_F]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

lemma act_mapB {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    act (⟨mapB, mapB_mem_F⟩ : FF) z = bFun z := by
  rw [act_of_mem _ hz]
  rfl

theorem exists_jump_half : ∃ b : FF, act b (1 / 2) = 1 / 2 ∧ jump b (1 / 2) ≠ 0 := by
  refine ⟨⟨mapB, mapB_mem_F⟩, ?_, ?_⟩
  · rw [act_mapB half_mem_UI]
    exact bFun_of_le_half le_rfl
  · have hR : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 4),
        act (⟨mapB, mapB_mem_F⟩ : FF) z = 2 ^ (-1 : ℤ) * z + 1 / 4 := by
      intro z hz
      rw [act_mapB ⟨by linarith [hz.1], by linarith [hz.2]⟩, bFun_of_mem1 hz.1 hz.2,
        zpow_neg_one]
      ring
    have hL : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2),
        act (⟨mapB, mapB_mem_F⟩ : FF) z = 2 ^ (0 : ℤ) * z + 0 := by
      intro z hz
      rw [act_mapB ⟨hz.1, by linarith [hz.2]⟩, bFun_of_le_half hz.2]
      simp
    unfold jump
    rw [log_derivWithin_Ici (by norm_num) hR, log_derivWithin_Iic (by norm_num) hL]
    norm_num

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias exists_jump_half := ThompsonAmenability.Kai.PartC.exists_jump_half

end ThompsonAmenability.Kai
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai.PartTW
/-! # Part T, from the published transience theorem `ThompsonWalk.summable_green_of_isStrictlyNondegenerate` -/
/-- The development's convolution powers agree with powers in the monoid algebra. -/
theorem cpow_eq_coeff_pow (μ : FF →₀ ℝ) (n : ℕ) :
    cpow μ n = ((MonoidAlgebra.ofCoeff μ) ^ n).coeff := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
    simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single]
    rw [← ih]
    rfl

theorem summable_hit (μ : FF →₀ ℝ) (hμ : IsProbability μ) (hnd : IsStrictlyNondegenerate μ)
    (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ IsDyadic y) (A : Finset ℝ) :
    Summable (fun n => hit μ n y A) := by
  refine (ThompsonWalk.summable_green_of_isStrictlyNondegenerate μ hμ hnd y hy A).congr fun n => ?_
  simp only [hit, cpow_eq_coeff_pow]
  rfl

end ThompsonAmenability.Kai.PartTW
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part T: transience -/
alias summable_hit := ThompsonAmenability.Kai.PartTW.summable_hit

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartS
open CannonFloydParry Filter Topology
open ThompsonAmenability.Kai
/-!
# Part S: the limit law

The law `pdist μ n g` of the configuration at `1/2` of `g * h`, `h ∼ μ^{*n}`, changes from step `n`
to step `n + 1` only on the event that the walk from `g⁻¹ (1/2)` sits in a fixed finite set `A` (the
images of the breakpoints of the elements of `supp μ`). Transience (`summable_hit`) makes these
changes summable in `ℓ¹(ℤ)`, so the laws converge in `ℓ¹` to a probability `p g`; harmonicity in `g`
passes to the limit from the finite identity `pdist μ (n+1) g = ∑ₛ μ s · pdist μ n (g * s)`.

Everything is phrased through the integral `E ν f = ∑ₕ ν h · f h` of a function against a finitely
supported weight; the two expansions of `E (cpow μ (n+1))` (append the new step on the right, by
definition, or on the left, by induction) replace the associativity of `conv`.
-/
/-! ## An abstract `ℓ¹` limit lemma -/
/-- Probability vectors on `ℤ` whose successive `ℓ¹` distances are summable converge pointwise to a
probability vector. -/
theorem limit_of_steps (f : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (hd : Summable d)
    (h0 : ∀ n k, 0 ≤ f n k) (h1 : ∀ n (K : Finset ℤ), ∑ k ∈ K, f n k ≤ 1)
    (h2 : ∀ n, ∃ K : Finset ℤ, ∑ k ∈ K, f n k = 1)
    (hstep : ∀ n (K : Finset ℤ), ∑ k ∈ K, |f (n + 1) k - f n k| ≤ d n) :
    ∃ p : ℤ → ℝ, (∀ k, Tendsto (fun n => f n k) atTop (𝓝 (p k))) ∧ HasSum p 1 ∧
      ∀ k, 0 ≤ p k ∧ p k ≤ 1 := by
  set e : ℤ → ℕ → ℝ := fun k n => |f (n + 1) k - f n k| with he
  have he_le : ∀ k n, e k n ≤ d n := fun k n => by
    simpa [he] using hstep n {k}
  have he_sum : ∀ k, Summable (e k) := fun k =>
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) (he_le k) hd
  have hdist : ∀ k n, dist (f n k) (f n.succ k) ≤ e k n := fun k n => by
    rw [Real.dist_eq, abs_sub_comm]
  have hcauchy : ∀ k, CauchySeq (fun n => f n k) := fun k =>
    cauchySeq_of_dist_le_of_summable (e k) (hdist k) (he_sum k)
  choose p hp using fun k => cauchySeq_tendsto_of_complete (hcauchy k)
  have htail : ∀ n (K : Finset ℤ), ∑ k ∈ K, |f n k - p k| ≤ ∑' m, d (m + n) := by
    intro n K
    have h3 : ∀ k, |f n k - p k| ≤ ∑' m, e k (m + n) := fun k => by
      rw [← Real.dist_eq]
      simpa [add_comm] using
        dist_le_tsum_of_dist_le_of_tendsto (e k) (hdist k) (he_sum k) (hp k) n
    have hs : ∀ k ∈ K, Summable (fun m => e k (m + n)) := fun k _ =>
      (summable_nat_add_iff n).mpr (he_sum k)
    calc ∑ k ∈ K, |f n k - p k| ≤ ∑ k ∈ K, ∑' m, e k (m + n) :=
          Finset.sum_le_sum fun k _ => h3 k
      _ = ∑' m, ∑ k ∈ K, e k (m + n) := (Summable.tsum_finsetSum hs).symm
      _ ≤ ∑' m, d (m + n) :=
          Summable.tsum_le_tsum (fun m => hstep (m + n) K) (summable_sum hs)
            ((summable_nat_add_iff n).mpr hd)
  have hr : Tendsto (fun n => ∑' m, d (m + n)) atTop (𝓝 0) := tendsto_sum_nat_add d
  have hp0 : ∀ k, 0 ≤ p k := fun k => ge_of_tendsto' (hp k) (fun n => h0 n k)
  have hK : ∀ K : Finset ℤ, ∑ k ∈ K, p k ≤ 1 := fun K =>
    le_of_tendsto' (tendsto_finsetSum K fun k _ => hp k) (fun n => h1 n K)
  have hsumm : Summable p := summable_of_sum_le (fun k => hp0 k) hK
  have hle : ∑' k, p k ≤ 1 := hsumm.tsum_le_of_sum_le hK
  have hge : ∀ n, 1 - ∑' m, d (m + n) ≤ ∑' k, p k := by
    intro n
    obtain ⟨K, hK1⟩ := h2 n
    have ha : ∑ k ∈ K, f n k - ∑ k ∈ K, p k ≤ ∑ k ∈ K, |f n k - p k| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun k _ => le_abs_self _
    have hb := htail n K
    have hc := hsumm.sum_le_tsum K (fun k _ => hp0 k)
    linarith
  have hge1 : 1 ≤ ∑' k, p k := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hr
    rw [sub_zero] at h
    exact le_of_tendsto' h hge
  refine ⟨p, hp, hsumm.hasSum_iff.mpr (le_antisymm hle hge1), fun k => ⟨hp0 k, ?_⟩⟩
  simpa using hK {k}

/-! ## Integration against finitely supported weights -/
/-- The integral of `f` against the finitely supported weight `ν`. -/
noncomputable def E (ν : FF →₀ ℝ) (f : FF → ℝ) : ℝ := ν.sum fun h w => w * f h

lemma E_eq (ν : FF →₀ ℝ) (f : FF → ℝ) : E ν f = ∑ h ∈ ν.support, ν h * f h := rfl

lemma E_single_one (f : FF → ℝ) : E (Finsupp.single 1 1) f = f 1 := by
  unfold E
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

lemma E_conv (ν μ : FF →₀ ℝ) (f : FF → ℝ) :
    E (conv ν μ) f = E ν (fun g => E μ (fun h => f (g * h))) := by
  unfold E conv
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  apply Finsupp.sum_congr
  intro g _
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro h _
  rw [Finsupp.sum_single_index (zero_mul _)]
  ring

lemma E_nonneg {ν : FF →₀ ℝ} (hν : ∀ h, 0 ≤ ν h) {f : FF → ℝ} (hf : ∀ h, 0 ≤ f h) :
    0 ≤ E ν f :=
  Finset.sum_nonneg fun h _ => mul_nonneg (hν h) (hf h)

lemma E_mono_on {ν : FF →₀ ℝ} (hν : ∀ h, 0 ≤ ν h) {f g : FF → ℝ}
    (hfg : ∀ h ∈ ν.support, f h ≤ g h) : E ν f ≤ E ν g :=
  Finset.sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (hfg h hh) (hν h)

lemma E_congr_on {ν : FF →₀ ℝ} {f g : FF → ℝ} (hfg : ∀ h ∈ ν.support, f h = g h) :
    E ν f = E ν g :=
  Finset.sum_congr rfl fun h hh => by simp only [hfg h hh]

lemma E_sub (ν : FF →₀ ℝ) (f g : FF → ℝ) : E ν f - E ν g = E ν (fun h => f h - g h) := by
  simp only [E_eq, mul_sub, Finset.sum_sub_distrib]

lemma E_const_mul (ν : FF →₀ ℝ) (c : ℝ) (f : FF → ℝ) : E ν (fun h => c * f h) = c * E ν f := by
  simp only [E_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

lemma E_abs {ν : FF →₀ ℝ} (hν : ∀ h, 0 ≤ ν h) (f : FF → ℝ) : |E ν f| ≤ E ν (fun h => |f h|) :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (le_of_eq (Finset.sum_congr rfl fun h _ => by rw [abs_mul, abs_of_nonneg (hν h)]))

lemma E_finset_sum {ι : Type*} (ν : FF →₀ ℝ) (K : Finset ι) (F : ι → FF → ℝ) :
    E ν (fun h => ∑ k ∈ K, F k h) = ∑ k ∈ K, E ν (F k) := by
  simp only [E_eq, Finset.mul_sum]
  exact Finset.sum_comm

lemma E_const {ν : FF →₀ ℝ} (h1 : E ν (fun _ => 1) = 1) (c : ℝ) : E ν (fun _ => c) = c := by
  simp only [E_eq, mul_one] at h1 ⊢
  rw [← Finset.sum_mul, h1, one_mul]

lemma E_sub_const {ν : FF →₀ ℝ} (h1 : E ν (fun _ => 1) = 1) (f : FF → ℝ) (c : ℝ) :
    E ν f - c = E ν (fun h => f h - c) := by
  have := E_sub ν f (fun _ => c)
  rwa [E_const h1] at this

lemma E_tendsto (ν : FF →₀ ℝ) {F : ℕ → FF → ℝ} {L : FF → ℝ}
    (h : ∀ s, Tendsto (fun n => F n s) atTop (𝓝 (L s))) :
    Tendsto (fun n => E ν (F n)) atTop (𝓝 (E ν L)) :=
  tendsto_finsetSum _ fun s _ => (h s).const_mul _

/-! ## Convolution powers -/
lemma E_cpow_zero (μ : FF →₀ ℝ) (f : FF → ℝ) : E (cpow μ 0) f = f 1 :=
  E_single_one f

/-- Appending the new step on the right (the definition of `cpow`). -/
lemma E_cpow_succ (μ : FF →₀ ℝ) (n : ℕ) (f : FF → ℝ) :
    E (cpow μ (n + 1)) f = E (cpow μ n) (fun h => E μ (fun s => f (h * s))) :=
  E_conv _ _ _

/-- Prepending the new step on the left. -/
lemma E_cpow_succ' (μ : FF →₀ ℝ) (n : ℕ) (f : FF → ℝ) :
    E (cpow μ (n + 1)) f = E μ (fun s => E (cpow μ n) (fun h => f (s * h))) := by
  induction n generalizing f with
  | zero => simp only [E_cpow_succ, E_cpow_zero, one_mul, mul_one]
  | succ n ih =>
    rw [E_cpow_succ, ih]
    simp only [E_cpow_succ, mul_assoc]

lemma E_mu_one {μ : FF →₀ ℝ} (hμ : IsProbability μ) : E μ (fun _ => 1) = 1 := by
  simpa [E, mul_one] using hμ.2

lemma E_cpow_one {μ : FF →₀ ℝ} (hμ : IsProbability μ) (n : ℕ) : E (cpow μ n) (fun _ => 1) = 1 := by
  induction n with
  | zero => exact E_cpow_zero μ _
  | succ n ih => rw [E_cpow_succ]; simp only [E_mu_one hμ]; exact ih

lemma E_cpow_nonneg {μ : FF →₀ ℝ} (hμ : IsProbability μ) (n : ℕ) {f : FF → ℝ}
    (hf : ∀ h, 0 ≤ f h) : 0 ≤ E (cpow μ n) f := by
  induction n generalizing f with
  | zero => rw [E_cpow_zero]; exact hf 1
  | succ n ih => rw [E_cpow_succ]; exact ih fun h => E_nonneg hμ.1 fun s => hf _

lemma cpow_nonneg {μ : FF →₀ ℝ} (hμ : IsProbability μ) (n : ℕ) (h : FF) : 0 ≤ cpow μ n h := by
  classical
  have hE := E_cpow_nonneg hμ n (f := fun x => if x = h then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have heq : E (cpow μ n) (fun x => if x = h then 1 else 0) = cpow μ n h := by
    rw [E_eq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    split_ifs with hne
    · rfl
    · exact (not_not.mp hne).symm
  rwa [heq] at hE

/-! ## The configuration cocycle and the bad set -/
lemma act_act_inv (h : FF) (t : ℝ) : act h (act h⁻¹ t) = t := by
  rw [← act_mul, mul_inv_cancel, act_one]

lemma cfg_mul (g h : FF) (y : ℝ) : cfg (g * h) y = cfg g y + cfg h (act g⁻¹ y) := by
  unfold cfg
  rw [mul_inv_rev, act_mul, jump_mul, act_act_inv, add_comm]

/-- The finite set of points where some `s ∈ supp μ` has a nonzero transported jump. -/
noncomputable def bad (μ : FF →₀ ℝ) : Finset ℝ :=
  μ.support.biUnion fun s => (finite_jump s).toFinset.image (act s)

lemma cfg_eq_zero (μ : FF →₀ ℝ) {s : FF} (hs : s ∈ μ.support) {z : ℝ} (hz : z ∉ bad μ) :
    cfg s z = 0 := by
  by_contra hne
  apply hz
  simp only [bad, Finset.mem_biUnion, Finset.mem_image, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  exact ⟨s, hs, act s⁻¹ z, hne, act_act_inv s z⟩

/-! ## The laws `pdist` -/
lemma pdist_eq (μ : FF →₀ ℝ) (n : ℕ) (g : FF) (k : ℤ) :
    pdist μ n g k = E (cpow μ n) (fun h => if cfg (g * h) (1 / 2) = k then 1 else 0) := by
  unfold pdist E
  apply Finsupp.sum_congr
  intro h _
  simp only [mul_ite, mul_one, mul_zero]

lemma hit_eq (μ : FF →₀ ℝ) (n : ℕ) (y : ℝ) (A : Finset ℝ) :
    hit μ n y A = E (cpow μ n) (fun h => if act h⁻¹ y ∈ A then 1 else 0) := by
  unfold hit E
  apply Finsupp.sum_congr
  intro h _
  simp only [mul_ite, mul_one, mul_zero]

lemma sum_pdist (μ : FF →₀ ℝ) (n : ℕ) (g : FF) (K : Finset ℤ) :
    ∑ k ∈ K, pdist μ n g k = E (cpow μ n) (fun h => if cfg (g * h) (1 / 2) ∈ K then 1 else 0) := by
  simp only [pdist_eq]
  rw [← E_finset_sum]
  congr 1
  funext h
  exact Finset.sum_ite_eq K _ _

lemma pdist_succ (μ : FF →₀ ℝ) (n : ℕ) (g : FF) (k : ℤ) :
    pdist μ (n + 1) g k = E μ (fun s => pdist μ n (g * s) k) := by
  rw [pdist_eq, E_cpow_succ']
  simp only [pdist_eq, mul_assoc]

lemma sum_abs_ind_sub_ind_le (K : Finset ℤ) (a b : ℤ) :
    ∑ k ∈ K, |(if a = k then (1 : ℝ) else 0) - (if b = k then 1 else 0)| ≤ 2 := by
  calc ∑ k ∈ K, |(if a = k then (1 : ℝ) else 0) - (if b = k then 1 else 0)|
      ≤ ∑ k ∈ K, ((if a = k then (1 : ℝ) else 0) + (if b = k then 1 else 0)) :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> norm_num
    _ = (if a ∈ K then 1 else 0) + (if b ∈ K then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    _ ≤ 2 := by split_ifs <;> norm_num

lemma pdist_step {μ : FF →₀ ℝ} (hμ : IsProbability μ) (g : FF) (n : ℕ) (K : Finset ℤ) :
    ∑ k ∈ K, |pdist μ (n + 1) g k - pdist μ n g k| ≤ 2 * hit μ n (act g⁻¹ (1 / 2)) (bad μ) := by
  set D : ℤ → FF → FF → ℝ := fun k h s =>
    (if cfg (g * (h * s)) (1 / 2) = k then 1 else 0) - (if cfg (g * h) (1 / 2) = k then 1 else 0)
    with hD
  have key : ∀ k, pdist μ (n + 1) g k - pdist μ n g k =
      E (cpow μ n) (fun h => E μ (fun s => D k h s)) := by
    intro k
    rw [pdist_eq, pdist_eq, E_cpow_succ, E_sub]
    congr 1
    funext h
    rw [E_sub_const (E_mu_one hμ)]
  have hpt : ∀ h, ∑ k ∈ K, |E μ (fun s => D k h s)| ≤
      2 * (if act h⁻¹ (act g⁻¹ (1 / 2)) ∈ bad μ then 1 else 0) := by
    intro h
    calc ∑ k ∈ K, |E μ (fun s => D k h s)| ≤ ∑ k ∈ K, E μ (fun s => |D k h s|) :=
          Finset.sum_le_sum fun k _ => E_abs hμ.1 _
      _ = E μ (fun s => ∑ k ∈ K, |D k h s|) := (E_finset_sum μ K _).symm
      _ ≤ E μ (fun _ => 2 * (if act h⁻¹ (act g⁻¹ (1 / 2)) ∈ bad μ then 1 else 0)) := by
          apply E_mono_on hμ.1
          intro s hs
          split_ifs with hA
          · simpa [hD] using sum_abs_ind_sub_ind_le K _ _
          · have hc : cfg (g * (h * s)) (1 / 2) = cfg (g * h) (1 / 2) := by
              rw [← mul_assoc, cfg_mul, mul_inv_rev, act_mul, cfg_eq_zero μ hs hA, add_zero]
            simp only [hD, hc, sub_self, abs_zero, Finset.sum_const_zero, mul_zero, le_refl]
      _ = 2 * (if act h⁻¹ (act g⁻¹ (1 / 2)) ∈ bad μ then 1 else 0) := E_const (E_mu_one hμ) _
  calc ∑ k ∈ K, |pdist μ (n + 1) g k - pdist μ n g k|
      = ∑ k ∈ K, |E (cpow μ n) (fun h => E μ (fun s => D k h s))| :=
        Finset.sum_congr rfl fun k _ => by rw [key]
    _ ≤ ∑ k ∈ K, E (cpow μ n) (fun h => |E μ (fun s => D k h s)|) :=
        Finset.sum_le_sum fun k _ => E_abs (cpow_nonneg hμ n) _
    _ = E (cpow μ n) (fun h => ∑ k ∈ K, |E μ (fun s => D k h s)|) := (E_finset_sum _ K _).symm
    _ ≤ E (cpow μ n) (fun h => 2 * (if act h⁻¹ (act g⁻¹ (1 / 2)) ∈ bad μ then 1 else 0)) :=
        E_mono_on (cpow_nonneg hμ n) fun h _ => hpt h
    _ = 2 * hit μ n (act g⁻¹ (1 / 2)) (bad μ) := by rw [E_const_mul, hit_eq]

/-! ## The limit law -/
theorem exists_limit_law (μ : FF →₀ ℝ) (hμ : IsProbability μ) (hnd : IsStrictlyNondegenerate μ) :
    ∃ p : FF → ℤ → ℝ, (∀ g k, Tendsto (fun n => pdist μ n g k) atTop (𝓝 (p g k))) ∧
      (∀ g, HasSum (p g) 1) ∧ (∀ g k, 0 ≤ p g k ∧ p g k ≤ 1) ∧
      (∀ g k, p g k = μ.sum fun s w => w * p (g * s) k) := by
  have hlim : ∀ g : FF, ∃ p : ℤ → ℝ, (∀ k, Tendsto (fun n => pdist μ n g k) atTop (𝓝 (p k))) ∧
      HasSum p 1 ∧ ∀ k, 0 ≤ p k ∧ p k ≤ 1 := by
    intro g
    have hy : 0 < act g⁻¹ (1 / 2) ∧ act g⁻¹ (1 / 2) < 1 ∧ IsDyadic (act g⁻¹ (1 / 2)) :=
      act_dyadic g⁻¹ ⟨by norm_num, by norm_num, ⟨1, 1, by norm_num⟩⟩
    refine limit_of_steps (fun n k => pdist μ n g k) (fun n => 2 * hit μ n (act g⁻¹ (1 / 2)) (bad μ))
      ((summable_hit μ hμ hnd _ hy (bad μ)).mul_left 2) ?_ ?_ ?_ (pdist_step hμ g)
    · intro n k
      rw [pdist_eq]
      exact E_cpow_nonneg hμ n fun h => by split_ifs <;> norm_num
    · intro n K
      rw [sum_pdist]
      exact (E_mono_on (cpow_nonneg hμ n) fun h _ => by split_ifs <;> norm_num).trans_eq
        (E_cpow_one hμ n)
    · intro n
      refine ⟨(cpow μ n).support.image fun h => cfg (g * h) (1 / 2), ?_⟩
      rw [sum_pdist]
      exact (E_congr_on fun h hh => if_pos (Finset.mem_image_of_mem _ hh)).trans (E_cpow_one hμ n)
  choose p hp using hlim
  refine ⟨p, fun g => (hp g).1, fun g => (hp g).2.1, fun g => (hp g).2.2, fun g k => ?_⟩
  have h1 : Tendsto (fun n => pdist μ (n + 1) g k) atTop (𝓝 (p g k)) :=
    ((hp g).1 k).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => pdist μ (n + 1) g k) atTop (𝓝 (E μ (fun s => p (g * s) k))) := by
    simp only [pdist_succ]
    exact E_tendsto μ fun s => (hp (g * s)).1 k
  exact tendsto_nhds_unique h1 h2

end ThompsonAmenability.Kai.PartS
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part S: the limit law -/
alias exists_limit_law := ThompsonAmenability.Kai.PartS.exists_limit_law

end ThompsonAmenability.Kai
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai.PartL
open ThompsonAmenability.Kai
/-- If `b` fixes `1/2`, the configuration of `b * h` at `1/2` is that of `h` shifted by
`jump b (1/2)`. -/
theorem cfg_mul_of_fix (b h : FF) (hb : act b (1 / 2) = 1 / 2) :
    cfg (b * h) (1 / 2) = cfg h (1 / 2) + jump b (1 / 2) := by
  have hbinv : act b⁻¹ (1 / 2) = 1 / 2 := by
    conv_lhs => rw [← hb]
    rw [← act_mul, inv_mul_cancel, act_one]
  have hh : act h (act h⁻¹ (1 / 2)) = 1 / 2 := by
    rw [← act_mul, mul_inv_cancel, act_one]
  unfold cfg
  rw [mul_inv_rev, act_mul, hbinv, jump_mul, hh]

theorem pdist_shift (μ : FF →₀ ℝ) (b : FF) (hb : act b (1 / 2) = 1 / 2) (n : ℕ) (k : ℤ) :
    pdist μ n b k = pdist μ n 1 (k - jump b (1 / 2)) := by
  unfold pdist
  refine Finsupp.sum_congr fun h _ => ?_
  rw [one_mul, cfg_mul_of_fix b h hb]
  congr 1
  apply propext
  constructor <;> intro H <;> omega

end ThompsonAmenability.Kai.PartL
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part L: the shift and the periodicity contradiction -/
alias pdist_shift := ThompsonAmenability.Kai.PartL.pdist_shift

end ThompsonAmenability.Kai
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai.PartL
open ThompsonAmenability.Kai
theorem false_of_periodic (p : ℤ → ℝ) (d : ℤ) (hd : d ≠ 0) (hper : ∀ k, p k = p (k - d))
    (hs : HasSum p 1) : False := by
  have hstep : ∀ k (m : ℕ), p (k + m * d) = p k := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hper, ← ih]
      congr 1
      push_cast
      ring
  have h0 : Tendsto p cofinite (𝓝 0) := hs.summable.tendsto_cofinite_zero
  have hzero : ∀ k, p k = 0 := by
    intro k
    have hinj : Function.Injective (fun m : ℕ => k + (m : ℤ) * d) := by
      intro m₁ m₂ h
      have : (m₁ : ℤ) * d = (m₂ : ℤ) * d := by simpa using h
      exact_mod_cast mul_right_cancel₀ hd this
    have ht : Tendsto (fun m : ℕ => p (k + (m : ℤ) * d)) atTop (𝓝 0) := by
      rw [← Nat.cofinite_eq_atTop]
      exact h0.comp hinj.tendsto_cofinite
    simp only [hstep] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have : p = 0 := funext hzero
  rw [this] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

end ThompsonAmenability.Kai.PartL
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
alias false_of_periodic := ThompsonAmenability.Kai.PartL.false_of_periodic

/-! ## Assembly -/

end ThompsonAmenability.Kai
end
end

section
open CannonFloydParry Filter Topology
open ThompsonAmenability
open ThompsonAmenability.Kai
theorem solution (μ : CannonFloydParry.F →₀ ℝ) (hμ : IsProbability μ)
    (hnd : IsStrictlyNondegenerate μ) : ¬ IsLiouville μ := by
  intro hL
  obtain ⟨p, hlim, hsum, hbd, hharm⟩ := exists_limit_law μ hμ hnd
  obtain ⟨b, hb, hj⟩ := exists_jump_half
  have hshift : ∀ k, p b k = p 1 (k - jump b (1 / 2)) := fun k =>
    tendsto_nhds_unique (hlim b k) (by simpa only [pdist_shift μ b hb] using hlim 1 (k - jump b (1 / 2)))
  have hmem : ∀ g : FF, g ∈ Subsemigroup.closure (μ.support : Set FF) := fun g => by
    rw [show Subsemigroup.closure (μ.support : Set FF) = ⊤ from hnd]; trivial
  have hconst : ∀ k, p b k = p 1 k := fun k =>
    hL (fun g => p g k) ⟨1, fun g _ => by rw [abs_le]; constructor <;> linarith [(hbd g k).1, (hbd g k).2]⟩
      (fun g _ => hharm g k) b (hmem b) 1 (hmem 1)
  exact false_of_periodic (p 1) (jump b (1 / 2)) hj
    (fun k => by rw [← hconst k, hshift k]) (hsum 1)
end
