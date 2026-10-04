-- Prove2me | solution 1 for ThompsonWalk.summable_green_of_isStrictlyNondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:24.902397+00:00
-- url     : https://prove2.me/submissions/c9c9b847-7116-4bf3-9c37-d952e59331cf

import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability
import Theorems.Thm_CannonFloydParry_bijOn_dyadic
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F
import Mathlib


section
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

lemma act_of_mem (g : FF) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    act g z = ((g : UI ≃o UI) ⟨z, hz⟩ : ℝ) :=
  extend_of_mem' _ hz

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

/-! ### Local affine structure of elements of `F` -/

/-! ### The cocycle -/

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartC
open CannonFloydParry Filter Topology
/-! ### The element `B` -/

end ThompsonAmenability.Kai.PartC
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai

end ThompsonAmenability.Kai
end

section
namespace ThompsonAmenability.Kai.PartT
open CannonFloydParry Filter Topology
/-!
# Part T: transience of the induced random walk on the dyadics of `(0,1)`

For a strictly non-degenerate probability `μ` on `F` and a dyadic `y ∈ (0,1)`, the walk
`y ↦ g⁻¹ y` (`g ∼ μ^{*n}`) visits every finite set only summably often (Kaimanovich, Theorems 14,
16, 25). The proof is analytic, with finitely supported functions on `ℝ` and no path space:

* **Dirichlet forms.** `D f g = ∑' z, (f z - f (g z))²` and `E μ f = ∑_h μ(h) D f h`.
  `D f (g h) ≤ 2 D f g + 2 D f h`, so by strict non-degeneracy, for every `g ∈ F` there is `C` with
  `D f g ≤ C · E μ f` for all `f`. (This replaces Kaimanovich's Theorem 16 and the measure `μ'`.)
* **Hardy inequality on a binary tree.** `t₀ = B` and `t₁ = B A⁻¹` act on `[1/2, 3/4]` as
  `x ↦ x/2 + 1/4` and `x ↦ x/2 + 3/8`. Below every dyadic `r ∈ (1/2, 3/4)` they span a binary tree
  of pairwise distinct points. Telescoping the level averages of `f` and Cauchy–Schwarz give
  `f(r)² ≤ D f t₀ + D f t₁`, which is the transience of the simple random walk (Theorems 13–14).
* **Transitivity.** `A^{±1}` and `B` move every dyadic of `(0,1)` into `(1/2, 3/4)`, so for every
  dyadic `o ∈ (0,1)` there is `C` with `f(o)² ≤ C · E μ f`.
* **Green function bound.** For `u_N = ∑_{n<N} μ^{*n} · δ_o` one has
  `E μ u_N = 2 ⟨u_N - P u_N, u_N⟩ = 2 (u_N(o) - ⟨μ^{*N} · δ_o, u_N⟩) ≤ 2 u_N(o)`
  (using `μ ⋆ μ^{*n} = μ^{*n} ⋆ μ`). Hence `u_N(o) ≤ 2C`, and `u_N(y)` is bounded through
  `D u_N g₀`, where `y = g₀ o`.
-/
/-! ## The action -/
lemma act_inv_act (g : FF) (x : ℝ) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

lemma act_act_inv (g : FF) (x : ℝ) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- `act g` as a permutation of `ℝ`. -/
noncomputable def actEquiv (g : FF) : ℝ ≃ ℝ where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv := act_act_inv g

@[simp] lemma actEquiv_apply (g : FF) (x : ℝ) : actEquiv g x = act g x := rfl

lemma act_injective (g : FF) : Function.Injective (act g) := (actEquiv g).injective

lemma act_inv_eq_iff (g : FF) (x y : ℝ) : act g⁻¹ y = x ↔ act g x = y := by
  constructor
  · rintro rfl; exact act_act_inv g y
  · rintro rfl; exact act_inv_act g x

/-! ## The generators `A`, `B` and the tree maps -/
lemma mapA_mem : mapA ∈ F := by
  rw [← closure_mapA_mapB_eq_F]; exact Subgroup.subset_closure (by simp)

lemma mapB_mem : mapB ∈ F := by
  rw [← closure_mapA_mapB_eq_F]; exact Subgroup.subset_closure (by simp)

/-- `A` as an element of `F`. -/
noncomputable def ea : FF := ⟨mapA, mapA_mem⟩

/-- `B` as an element of `F`. -/
noncomputable def eb : FF := ⟨mapB, mapB_mem⟩

lemma act_ea (x : ℝ) : act ea x = aFun x := by
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · simp only [act, ea, extend_apply, extendFun_of_mem _ h]
    rfl
  · simp only [act, ea, extend_apply, extendFun_of_notMem _ h]
    rcases not_and_or.mp h with h | h
    · exact (aFun_of_le_zero (le_of_lt (not_le.mp h))).symm
    · exact (aFun_of_one_le (le_of_lt (not_le.mp h))).symm

lemma act_eb (x : ℝ) : act eb x = bFun x := by
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · simp only [act, eb, extend_apply, extendFun_of_mem _ h]
    rfl
  · simp only [act, eb, extend_apply, extendFun_of_notMem _ h]
    rcases not_and_or.mp h with h | h
    · exact (bFun_of_le_half (by linarith [not_le.mp h])).symm
    · exact (bFun_of_one_le (le_of_lt (not_le.mp h))).symm

lemma act_ea_inv_of_eq {x w : ℝ} (h : aFun w = x) : act ea⁻¹ x = w := by
  rw [← h, ← act_ea, act_inv_act]

lemma act_ea_inv_low {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1/4) : act ea⁻¹ x = 2 * x :=
  act_ea_inv_of_eq (by rw [aFun_of_mem1 (by linarith) (by linarith)]; ring)

lemma act_ea_inv_mid {x : ℝ} (h0 : 1/4 ≤ x) (h1 : x ≤ 1/2) : act ea⁻¹ x = x + 1/4 :=
  act_ea_inv_of_eq (by rw [aFun_of_mem2 (by linarith) (by linarith)]; ring)

lemma act_ea_inv_high {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x ≤ 1) : act ea⁻¹ x = (x + 1) / 2 :=
  act_ea_inv_of_eq (by rw [aFun_of_mem3 (by linarith) (by linarith)]; ring)

/-- First tree map: `x ↦ x/2 + 1/4` on `[1/2, 3/4]`. -/
noncomputable def t0 : FF := eb

/-- Second tree map: `x ↦ x/2 + 3/8` on `[1/2, 3/4]`. -/
noncomputable def t1 : FF := eb * ea⁻¹

lemma act_t0 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x ≤ 3/4) : act t0 x = x / 2 + 1/4 := by
  rw [t0, act_eb, bFun_of_mem1 h0 h1]

lemma act_t1 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x ≤ 3/4) : act t1 x = x / 2 + 3/8 := by
  rw [t1, act_mul, act_ea_inv_high h0 (by linarith), act_eb,
    bFun_of_mem2 (by linarith) (by linarith)]
  ring

/-! ## Finitely supported functions -/
/-- `f` has finite support. -/
def FS (f : ℝ → ℝ) : Prop := (Function.support f).Finite

lemma FS.summable {f : ℝ → ℝ} (hf : FS f) : Summable f :=
  summable_of_ne_finset_zero (s := Set.Finite.toFinset (s := Function.support f) hf)
    (fun b hb => by
      by_contra hne
      exact hb ((Set.Finite.mem_toFinset _).mpr hne))

lemma FS.of_zero {f f' g : ℝ → ℝ} (hf : FS f) (hf' : FS f')
    (h : ∀ z, f z = 0 → f' z = 0 → g z = 0) : FS g := by
  refine (hf.union hf').subset ?_
  intro z hz
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
  exact hz (h z hc.1 hc.2)

lemma FS.comp_act {f : ℝ → ℝ} (hf : FS f) (g : FF) : FS (fun z => f (act g z)) := by
  have : (Function.support fun z => f (act g z)) = act g ⁻¹' Function.support f := rfl
  rw [FS, this]
  exact hf.preimage (act_injective g).injOn

/-! ## Dirichlet forms -/
/-- The Dirichlet form of `f` along `g`. -/
noncomputable def D (f : ℝ → ℝ) (g : FF) : ℝ := ∑' z, (f z - f (act g z)) ^ 2

/-- The Dirichlet form of `f` for the measure `μ`. -/
noncomputable def E (μ : FF →₀ ℝ) (f : ℝ → ℝ) : ℝ := μ.sum fun h w => w * D f h

lemma FS.sq_diff {f : ℝ → ℝ} (hf : FS f) (g : FF) : FS (fun z => (f z - f (act g z)) ^ 2) :=
  hf.of_zero (hf.comp_act g) (fun z h1 h2 => by simp [h1, h2])

lemma D_nonneg (f : ℝ → ℝ) (g : FF) : 0 ≤ D f g := tsum_nonneg fun _ => sq_nonneg _

lemma term_le_D {f : ℝ → ℝ} (hf : FS f) (g : FF) (z : ℝ) : (f z - f (act g z)) ^ 2 ≤ D f g :=
  (hf.sq_diff g).summable.le_tsum z (fun _ _ => sq_nonneg _)

lemma D_mul {f : ℝ → ℝ} (hf : FS f) (g h : FF) : D f (g * h) ≤ 2 * D f g + 2 * D f h := by
  have hs1 := (hf.sq_diff h).summable
  have hs2 : Summable fun z => (f (act h z) - f (act g (act h z))) ^ 2 :=
    ((hf.comp_act h).of_zero ((hf.comp_act g).comp_act h)
      (fun z h1 h2 => by simp [h1, h2])).summable
  have key : D f g = ∑' z, (f (act h z) - f (act g (act h z))) ^ 2 :=
    ((actEquiv h).tsum_eq (fun w => (f w - f (act g w)) ^ 2)).symm
  have hle : ∀ z, (f z - f (act (g * h) z)) ^ 2 ≤
      2 * (f (act h z) - f (act g (act h z))) ^ 2 + 2 * (f z - f (act h z)) ^ 2 := by
    intro z
    rw [act_mul]
    nlinarith [sq_nonneg ((f z - f (act h z)) - (f (act h z) - f (act g (act h z))))]
  calc D f (g * h) ≤ ∑' z, (2 * (f (act h z) - f (act g (act h z))) ^ 2
        + 2 * (f z - f (act h z)) ^ 2) :=
        Summable.tsum_le_tsum hle (hf.sq_diff (g * h)).summable
          ((hs2.mul_left 2).add (hs1.mul_left 2))
    _ = 2 * D f g + 2 * D f h := by
        rw [Summable.tsum_add (hs2.mul_left 2) (hs1.mul_left 2), Summable.tsum_mul_left _ hs2,
          Summable.tsum_mul_left _ hs1, key, D]

lemma E_nonneg {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (f : ℝ → ℝ) : 0 ≤ E μ f :=
  Finset.sum_nonneg fun h _ => mul_nonneg (hμ0 h) (D_nonneg f h)

/-- Comparison: along any element of the semigroup generated by `supp μ`, the Dirichlet form is
controlled by that of `μ`. -/
lemma D_le_E {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) {g : FF}
    (hg : g ∈ Subsemigroup.closure (μ.support : Set FF)) :
    ∃ C, 0 ≤ C ∧ ∀ f, FS f → D f g ≤ C * E μ f := by
  induction hg using Subsemigroup.closure_induction with
  | mem x hx =>
    have hx' : x ∈ μ.support := hx
    have hpos : 0 < μ x := lt_of_le_of_ne (hμ0 x) (Ne.symm (Finsupp.mem_support_iff.mp hx'))
    refine ⟨1 / μ x, by positivity, fun f _ => ?_⟩
    have : μ x * D f x ≤ E μ f :=
      Finset.single_le_sum (f := fun h => μ h * D f h)
        (fun h _ => mul_nonneg (hμ0 h) (D_nonneg f h)) hx'
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    linarith
  | mul x y _ _ hx hy =>
    obtain ⟨Cx, hCx, hx⟩ := hx
    obtain ⟨Cy, hCy, hy⟩ := hy
    refine ⟨2 * Cx + 2 * Cy, by positivity, fun f hf => ?_⟩
    have := D_mul hf x y
    have h1 := hx f hf
    have h2 := hy f hf
    nlinarith

/-! ## The Hardy inequality on the binary tree below a dyadic of `(1/2, 3/4)` -/
/-- The `j`-th point of level `ℓ` of the binary tree below `r`: in the coordinate
`s = 4x - 2 ∈ (0,1)` it is `(s_r + j) / 2^ℓ`. -/
noncomputable def tp (r : ℝ) (ℓ j : ℕ) : ℝ := 1/2 + (4 * r - 2 + j) / 2 ^ (ℓ + 2)

lemma tp_zero (r : ℝ) : tp r 0 0 = r := by
  simp only [tp, Nat.cast_zero, add_zero, zero_add]; ring

lemma tp_mem {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    1/2 < tp r ℓ j ∧ tp r ℓ j < 3/4 := by
  have hj' : (j : ℝ) + 1 ≤ 2 ^ ℓ := by exact_mod_cast hj
  have h2 : (0:ℝ) < 2 ^ (ℓ + 2) := by positivity
  have hpow : (2:ℝ) ^ (ℓ + 2) = 4 * 2 ^ ℓ := by ring
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  unfold tp
  constructor
  · have : 0 < (4 * r - 2 + j) / 2 ^ (ℓ + 2) := div_pos (by linarith) h2
    linarith
  · have : (4 * r - 2 + j) / 2 ^ (ℓ + 2) < 1/4 := by
      rw [div_lt_iff₀ h2, hpow]; linarith
    linarith

lemma tp_t0 {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    act t0 (tp r ℓ j) = tp r (ℓ + 1) j := by
  obtain ⟨h0, h1⟩ := tp_mem hr hj
  rw [act_t0 h0.le h1.le]
  unfold tp
  rw [show (2:ℝ) ^ (ℓ + 1 + 2) = 2 ^ (ℓ + 2) * 2 by ring]
  field_simp
  ring

lemma tp_t1 {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    act t1 (tp r ℓ j) = tp r (ℓ + 1) (2 ^ ℓ + j) := by
  obtain ⟨h0, h1⟩ := tp_mem hr hj
  rw [act_t1 h0.le h1.le]
  unfold tp
  rw [show (2:ℝ) ^ (ℓ + 1 + 2) = 2 ^ ℓ * 8 by ring, show (2:ℝ) ^ (ℓ + 2) = 2 ^ ℓ * 4 by ring]
  push_cast
  field_simp
  ring

/-- A dyadic `s ∈ (0,1)` is never a rational with odd denominator `2^m - 1`. -/
lemma no_int {s : ℝ} (h0 : 0 < s) (h1 : s < 1) {k m : ℕ} (hm : 1 ≤ m) {p q : ℤ}
    (hp : (2:ℝ) ^ k * s = p) (hq : ((2:ℝ) ^ m - 1) * s = q) : False := by
  have hc : IsCoprime ((2:ℤ) ^ m - 1) ((2:ℤ) ^ k) := by
    apply IsCoprime.pow_right
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ⟨-1, 2 ^ m', by ring⟩
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a:ℝ) * ((2:ℝ) ^ m - 1) + (b:ℝ) * (2:ℝ) ^ k = 1 := by exact_mod_cast hab
  have hs : s = ((a * q + b * p : ℤ) : ℝ) := by
    push_cast
    rw [← hq, ← hp]
    linear_combination (-s) * hab'
  rw [hs] at h0 h1
  have h0' : 0 < a * q + b * p := by exact_mod_cast h0
  have h1' : a * q + b * p < 1 := by exact_mod_cast h1
  omega

lemma tp_level {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) (hd : IsDyadic r) {ℓ j ℓ' j' : ℕ}
    (h : tp r ℓ j = tp r ℓ' j') (hl : ℓ ≤ ℓ') : ℓ = ℓ' := by
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, ℓ' = ℓ + m := ⟨ℓ' - ℓ, by omega⟩
  have hm : 1 ≤ m := by omega
  obtain ⟨p, k, hpk⟩ := hd
  set s := 4 * r - 2 with hs_def
  have h2 : (0:ℝ) < 2 ^ (ℓ + 2) := by positivity
  have h2m : (0:ℝ) < 2 ^ m := by positivity
  have hmain : (s + j) * 2 ^ m = s + j' := by
    unfold tp at h
    rw [show (2:ℝ) ^ (ℓ + m + 2) = 2 ^ (ℓ + 2) * 2 ^ m by ring] at h
    field_simp at h
    linarith
  refine no_int (s := s) (by rw [hs_def]; linarith) (by rw [hs_def]; linarith) hm
    (k := k) (p := 4 * p - 2 * 2 ^ k) (q := (j' : ℤ) - 2 ^ m * j) ?_ ?_
  · rw [hs_def, hpk]
    have : (2:ℝ) ^ k ≠ 0 := by positivity
    push_cast
    field_simp
  · push_cast
    linear_combination hmain

lemma tp_inj {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) (hd : IsDyadic r) {ℓ j ℓ' j' : ℕ}
    (h : tp r ℓ j = tp r ℓ' j') : ℓ = ℓ' ∧ j = j' := by
  have hl : ℓ = ℓ' := by
    rcases le_total ℓ ℓ' with hl | hl
    · exact tp_level hr hd h hl
    · exact (tp_level hr hd h.symm hl).symm
  subst hl
  refine ⟨rfl, ?_⟩
  unfold tp at h
  have h2 : (0:ℝ) < 2 ^ (ℓ + 2) := by positivity
  have : (j : ℝ) = j' := by
    have := h
    field_simp at this
    linarith
  exact_mod_cast this

/-- **Hardy inequality on the tree** (transience of the simple random walk): for every dyadic
`r ∈ (1/2, 3/4)` and finitely supported `f`, `f(r)² ≤ D f t₀ + D f t₁`. -/
theorem tree_hardy {r : ℝ} (hr : 1/2 < r ∧ r < 3/4) (hd : IsDyadic r) {f : ℝ → ℝ} (hf : FS f) :
    f r ^ 2 ≤ D f t0 + D f t1 := by
  set d0 : ℝ → ℝ := fun z => f z - f (act t0 z) with hd0
  set d1 : ℝ → ℝ := fun z => f z - f (act t1 z) with hd1
  set Fl : ℕ → ℝ := fun ℓ => (1 / 2 ^ ℓ) * ∑ j ∈ Finset.range (2 ^ ℓ), f (tp r ℓ j) with hFl
  -- one level of the telescoping
  have hstep : ∀ ℓ, Fl ℓ - Fl (ℓ + 1) = ∑ j ∈ Finset.range (2 ^ ℓ),
      (1 / 2 ^ (ℓ + 1)) * (d0 (tp r ℓ j) + d1 (tp r ℓ j)) := by
    intro ℓ
    have hsplit : ∑ j ∈ Finset.range (2 ^ (ℓ + 1)), f (tp r (ℓ + 1) j) =
        ∑ j ∈ Finset.range (2 ^ ℓ), (f (act t0 (tp r ℓ j)) + f (act t1 (tp r ℓ j))) := by
      rw [show 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ by ring, Finset.sum_range_add,
        Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => by
          rw [tp_t0 hr (Finset.mem_range.mp hj)]
      · exact Finset.sum_congr rfl fun j hj => by
          rw [tp_t1 hr (Finset.mem_range.mp hj)]
    simp only [hFl]
    rw [hsplit, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hd0, hd1]
    rw [pow_succ]
    field_simp
    ring
  -- the telescoped identity, as a sum over the first `M` levels
  have hF0 : Fl 0 = f r := by simp [hFl, tp_zero]
  set S : ℕ → Finset (Σ _ : ℕ, ℕ) := fun M =>
    (Finset.range M).sigma (fun ℓ => Finset.range (2 ^ ℓ)) with hS
  have htel : ∀ M, f r - Fl M = ∑ p ∈ S M,
      (1 / 2 ^ (p.1 + 1)) * (d0 (tp r p.1 p.2) + d1 (tp r p.1 p.2)) := by
    intro M
    rw [← hF0, ← Finset.sum_range_sub', hS, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun ℓ _ => hstep ℓ
  have hinj : ∀ M, Set.InjOn (fun p : (Σ _ : ℕ, ℕ) => tp r p.1 p.2) ↑(S M) := by
    rintro M ⟨ℓ, j⟩ _ ⟨ℓ', j'⟩ _ h
    obtain ⟨rfl, rfl⟩ := tp_inj hr hd h
    rfl
  -- the energy bound for each `M`
  have hsum0 : Summable fun z => d0 z ^ 2 := (hf.sq_diff t0).summable
  have hsum1 : Summable fun z => d1 z ^ 2 := (hf.sq_diff t1).summable
  have hbound : ∀ M, (f r - Fl M) ^ 2 ≤ D f t0 + D f t1 := by
    intro M
    rw [htel M]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    have ha : ∑ p ∈ S M, (1 / (2:ℝ) ^ (p.1 + 1)) ^ 2 ≤ 1 / 2 := by
      rw [hS, Finset.sum_sigma]
      have : ∀ ℓ ∈ Finset.range M, ∑ j ∈ Finset.range (2 ^ ℓ), (1 / (2:ℝ) ^ (ℓ + 1)) ^ 2
          = 1 / 4 * (1 / 2) ^ ℓ := by
        intro ℓ _
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [one_div_pow (2:ℝ) ℓ]
        field_simp
        ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      have := sum_geometric_two_le M
      linarith
    have hb : ∑ p ∈ S M, (d0 (tp r p.1 p.2) + d1 (tp r p.1 p.2)) ^ 2 ≤
        2 * ∑ p ∈ S M, (d0 (tp r p.1 p.2) ^ 2 + d1 (tp r p.1 p.2) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p _ => by
        nlinarith [sq_nonneg (d0 (tp r p.1 p.2) - d1 (tp r p.1 p.2))]
    have hc : ∑ p ∈ S M, (d0 (tp r p.1 p.2) ^ 2 + d1 (tp r p.1 p.2) ^ 2) ≤
        D f t0 + D f t1 := by
      have := Finset.sum_image (f := fun z => d0 z ^ 2 + d1 z ^ 2) (hinj M)
      rw [← this]
      refine ((hsum0.add hsum1).sum_le_tsum _ (fun z _ => by positivity)).trans ?_
      rw [Summable.tsum_add hsum0 hsum1]
      rfl
    have hb0 : 0 ≤ ∑ p ∈ S M, (d0 (tp r p.1 p.2) + d1 (tp r p.1 p.2)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  -- the level averages tend to `0`
  have habs : Summable fun z => |f z| :=
    (hf.of_zero hf (fun z h _ => by simp [h])).summable
  have hlevel : ∀ M, |Fl M| ≤ (1 / 2) ^ M * ∑' z, |f z| := by
    intro M
    simp only [hFl]
    rw [abs_mul, abs_of_pos (by positivity), one_div_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hinjM : Set.InjOn (tp r M) ↑(Finset.range (2 ^ M)) := fun j _ j' _ h =>
      (tp_inj hr hd h).2
    rw [← Finset.sum_image (f := fun z => |f z|) hinjM]
    exact habs.sum_le_tsum _ (fun z _ => abs_nonneg _)
  have hlim : Tendsto Fl atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun M => (1 / 2) ^ M * ∑' z, |f z|)
      (fun M => by rw [Real.norm_eq_abs]; exact hlevel M) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const (∑' z, |f z|)
  have hT : Tendsto (fun M => (f r - Fl M) ^ 2) atTop (𝓝 ((f r - 0) ^ 2)) :=
    (tendsto_const_nhds.sub hlim).pow 2
  simpa using le_of_tendsto' hT hbound

/-! ## Moving any dyadic of `(0,1)` into `(1/2, 3/4)` -/
lemma to_tree_low : ∀ k : ℕ, ∀ y : ℝ, 0 < y → y ≤ 1/2 → (1/2 : ℝ) ^ (k + 2) < y →
    ∃ g : FF, 1/2 < act g y ∧ act g y ≤ 3/4 := by
  intro k
  induction k with
  | zero =>
    intro y _ h1 hk
    norm_num at hk
    refine ⟨ea⁻¹, ?_⟩
    rw [act_ea_inv_mid hk.le h1]
    constructor <;> linarith
  | succ k ih =>
    intro y h0 h1 hk
    by_cases hy : 1/4 < y
    · refine ⟨ea⁻¹, ?_⟩
      rw [act_ea_inv_mid hy.le h1]
      constructor <;> linarith
    · replace hy : y ≤ 1/4 := not_lt.mp hy
      have hk' : (1/2 : ℝ) ^ (k + 2) < 2 * y := by
        rw [show (1/2 : ℝ) ^ (k + 1 + 2) = (1/2) ^ (k + 2) * (1/2) by ring] at hk
        linarith
      obtain ⟨g, hg⟩ := ih (2 * y) (by linarith) (by linarith) hk'
      refine ⟨g * ea⁻¹, ?_⟩
      rw [act_mul, act_ea_inv_low h0.le hy]
      exact hg

lemma to_tree_high : ∀ k : ℕ, ∀ y : ℝ, 1/2 ≤ y → y < 1 → (1/2 : ℝ) ^ (k + 2) < 1 - y →
    ∃ g : FF, 1/2 ≤ act g y ∧ act g y < 3/4 := by
  intro k
  induction k with
  | zero =>
    intro y h0 _ hk
    norm_num at hk
    exact ⟨1, by rw [act_one]; constructor <;> linarith⟩
  | succ k ih =>
    intro y h0 h1 hk
    by_cases hy : y < 3/4
    · exact ⟨1, by rw [act_one]; exact ⟨h0, hy⟩⟩
    · replace hy : 3/4 ≤ y := not_lt.mp hy
      have hk' : (1/2 : ℝ) ^ (k + 2) < 1 - (2 * y - 1) := by
        rw [show (1/2 : ℝ) ^ (k + 1 + 2) = (1/2) ^ (k + 2) * (1/2) by ring] at hk
        linarith
      obtain ⟨g, hg⟩ := ih (2 * y - 1) (by linarith) (by linarith) hk'
      refine ⟨g * ea, ?_⟩
      rw [act_mul, act_ea, aFun_of_mem3 hy h1.le]
      exact hg

lemma to_tree_fix {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x ≤ 3/4) :
    ∃ g : FF, 1/2 < act g x ∧ act g x < 3/4 := by
  rcases h0.lt_or_eq with h0 | rfl
  · rcases h1.lt_or_eq with h1 | rfl
    · exact ⟨1, by rw [act_one]; exact ⟨h0, h1⟩⟩
    · exact ⟨t0, by rw [act_t0 (by norm_num) le_rfl]; norm_num⟩
  · exact ⟨t1, by rw [act_t1 le_rfl (by norm_num)]; norm_num⟩

/-- Every point of `(0,1)` is moved into `(1/2, 3/4)` by some element of `F`. -/
lemma to_tree {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    ∃ g : FF, 1/2 < act g y ∧ act g y < 3/4 := by
  rcases le_or_gt y (1/2) with hy | hy
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 (by norm_num : (1/2 : ℝ) < 1)
    have hk2 : (1/2 : ℝ) ^ (k + 2) < y :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk
    obtain ⟨g, hg⟩ := to_tree_low k y h0 hy hk2
    obtain ⟨g', hg'⟩ := to_tree_fix hg.1.le hg.2
    exact ⟨g' * g, by rw [act_mul]; exact hg'⟩
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < 1 - y)
      (by norm_num : (1/2 : ℝ) < 1)
    have hk2 : (1/2 : ℝ) ^ (k + 2) < 1 - y :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk
    obtain ⟨g, hg⟩ := to_tree_high k y hy.le h1 hk2
    obtain ⟨g', hg'⟩ := to_tree_fix hg.1 hg.2.le
    exact ⟨g' * g, by rw [act_mul]; exact hg'⟩

/-! ## The Hardy inequality at every dyadic of `(0,1)` -/
lemma mem_closure_of_nd {μ : FF →₀ ℝ} (hnd : IsStrictlyNondegenerate μ) (g : FF) :
    g ∈ Subsemigroup.closure (μ.support : Set FF) := by
  rw [show Subsemigroup.closure (μ.support : Set FF) = ⊤ from hnd]; trivial

/-- For every dyadic `o ∈ (0,1)`, `f(o)² ≤ C · E μ f` for all finitely supported `f`. -/
theorem hardy {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (hnd : IsStrictlyNondegenerate μ) {o : ℝ}
    (ho : 0 < o ∧ o < 1 ∧ IsDyadic o) : ∃ C, 0 ≤ C ∧ ∀ f, FS f → f o ^ 2 ≤ C * E μ f := by
  obtain ⟨g, hg⟩ := to_tree ho.1 ho.2.1
  have hrd : IsDyadic (act g o) := (act_dyadic g ho).2.2
  obtain ⟨C0, hC0, h0⟩ := D_le_E hμ0 (mem_closure_of_nd hnd t0)
  obtain ⟨C1, hC1, h1⟩ := D_le_E hμ0 (mem_closure_of_nd hnd t1)
  obtain ⟨C2, hC2, h2⟩ := D_le_E hμ0 (mem_closure_of_nd hnd g⁻¹)
  refine ⟨2 * C0 + 2 * C1 + 2 * C2, by positivity, fun f hf => ?_⟩
  have ht := tree_hardy hg hrd hf
  have hterm := term_le_D hf g⁻¹ (act g o)
  rw [act_inv_act] at hterm
  have e0 := h0 f hf
  have e1 := h1 f hf
  have e2 := h2 f hf
  nlinarith [sq_nonneg (2 * f (act g o) - f o)]

/-! ## Convolution powers -/
/-- Integration of `φ` against `ν`. -/
noncomputable def L (ν : FF →₀ ℝ) (φ : FF → ℝ) : ℝ := ν.sum fun g w => w * φ g

lemma L_conv (ν₁ ν₂ : FF →₀ ℝ) (φ : FF → ℝ) :
    L (conv ν₁ ν₂) φ = L ν₁ (fun h => L ν₂ (fun g => φ (h * g))) := by
  unfold L conv
  rw [Finsupp.sum_sum_index (by simp) (by intros; ring)]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [Finsupp.sum_sum_index (by simp) (by intros; ring), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  ring

lemma L_single_one (φ : FF → ℝ) : L (Finsupp.single 1 1) φ = φ 1 := by
  unfold L
  rw [Finsupp.sum_single_index (by simp)]
  ring

/-- `μ ⋆ μ^{*n} = μ^{*(n+1)}`, tested against every function. -/
lemma L_conv_comm (μ : FF →₀ ℝ) (n : ℕ) (φ : FF → ℝ) :
    L (conv μ (cpow μ n)) φ = L (cpow μ (n + 1)) φ := by
  induction n generalizing φ with
  | zero =>
    show L (conv μ (Finsupp.single 1 1)) φ = L (conv (Finsupp.single 1 1) μ) φ
    rw [L_conv, L_conv, L_single_one]
    simp only [L_single_one, mul_one, one_mul]
  | succ n ih =>
    show L (conv μ (conv (cpow μ n) μ)) φ = L (conv (cpow μ (n + 1)) μ) φ
    rw [L_conv, L_conv, ← ih, L_conv]
    simp only [L_conv, mul_assoc]

lemma L_nonneg {ν : FF →₀ ℝ} (hν : ∀ g, 0 ≤ ν g) {φ : FF → ℝ} (hφ : ∀ g, 0 ≤ φ g) :
    0 ≤ L ν φ :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hν g) (hφ g)

open Classical in
lemma L_eval (ν : FF →₀ ℝ) (x : FF) : L ν (fun g => if g = x then 1 else 0) = ν x := by
  unfold L
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finsupp.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

lemma cpow_nonneg {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (n : ℕ) : ∀ g, 0 ≤ cpow μ n g := by
  classical
  induction n with
  | zero =>
    intro g
    show 0 ≤ Finsupp.single 1 1 g
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    intro g
    show 0 ≤ conv (cpow μ n) μ g
    rw [← L_eval, L_conv]
    exact L_nonneg ih fun h => L_nonneg hμ0 fun k => by split_ifs <;> norm_num

lemma L_finset_sum (ν : FF →₀ ℝ) {ι : Type*} (s : Finset ι) (φ : ι → FF → ℝ) :
    L ν (fun g => ∑ i ∈ s, φ i g) = ∑ i ∈ s, L ν (φ i) := by
  unfold L Finsupp.sum
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-! ## The Green function bound -/
/-- `(μ^{*n} · δ_o)(z)`: the probability that `g o = z` for `g ∼ μ^{*n}`. -/
noncomputable def pn (μ : FF →₀ ℝ) (o : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  L (cpow μ n) (fun g => if act g o = z then 1 else 0)

/-- The truncated Green function `u_N = ∑_{n<N} μ^{*n} · δ_o`. -/
noncomputable def uN (μ : FF →₀ ℝ) (o : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, pn μ o n z

lemma pn_nonneg {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (o : ℝ) (n : ℕ) (z : ℝ) :
    0 ≤ pn μ o n z :=
  L_nonneg (cpow_nonneg hμ0 n) fun g => by split_ifs <;> norm_num

lemma uN_nonneg {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (o : ℝ) (N : ℕ) (z : ℝ) :
    0 ≤ uN μ o N z :=
  Finset.sum_nonneg fun n _ => pn_nonneg hμ0 o n z

lemma pn_FS (μ : FF →₀ ℝ) (o : ℝ) (n : ℕ) : FS (pn μ o n) := by
  classical
  refine ((cpow μ n).support.image (fun g => act g o)).finite_toSet.subset ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Finset.coe_image]
  by_contra hc
  apply hz
  unfold pn L Finsupp.sum
  refine Finset.sum_eq_zero fun g hg => ?_
  dsimp only
  rw [if_neg (fun h => hc ⟨g, hg, h⟩), mul_zero]

lemma pn_zero (μ : FF →₀ ℝ) (o z : ℝ) : pn μ o 0 z = if o = z then 1 else 0 := by
  show L (Finsupp.single 1 1) _ = _
  rw [L_single_one, act_one]

lemma uN_FS (μ : FF →₀ ℝ) (o : ℝ) (N : ℕ) : FS (uN μ o N) := by
  induction N with
  | zero =>
    have : uN μ o 0 = fun _ => 0 := funext fun z => by simp [uN]
    rw [this]
    simp [FS]
  | succ N ih =>
    have : uN μ o (N + 1) = fun z => uN μ o N z + pn μ o N z :=
      funext fun z => Finset.sum_range_succ _ _
    rw [this]
    exact ih.of_zero (pn_FS μ o N) (fun z h1 h2 => by simp [h1, h2])

lemma FS.mul_left {f : ℝ → ℝ} (hf : FS f) (g : ℝ → ℝ) : FS (fun z => g z * f z) :=
  hf.of_zero hf (fun z h _ => by simp [h])

/-- `P u_N = ∑_{n<N} μ^{*(n+1)} · δ_o`, where `(P f)(z) = ∑_h μ(h) f(h⁻¹ z)`. -/
lemma P_uN (μ : FF →₀ ℝ) (o : ℝ) (N : ℕ) (z : ℝ) :
    L μ (fun h => uN μ o N (act h⁻¹ z)) = ∑ n ∈ Finset.range N, pn μ o (n + 1) z := by
  unfold uN
  rw [L_finset_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold pn
  rw [← L_conv_comm, L_conv]
  congr 1
  funext h
  congr 1
  funext g
  have : (act g o = act h⁻¹ z) ↔ (act (h * g) o = z) := by
    rw [eq_comm, act_inv_eq_iff, act_mul]
  simp only [this]

/-- The key identity: `E μ u_N = 2 ⟨u_N - P u_N, u_N⟩ = 2 (u_N(o) - ⟨μ^{*N} · δ_o, u_N⟩)`. -/
lemma E_uN_le {μ : FF →₀ ℝ} (hμ : IsProbability μ) (o : ℝ) (N : ℕ) :
    E μ (uN μ o N) ≤ 2 * uN μ o N o := by
  set u := uN μ o N with hu_def
  have hu : FS u := uN_FS μ o N
  set Q := ∑' z, u z ^ 2 with hQ
  set R : FF → ℝ := fun h => ∑' z, u (act h⁻¹ z) * u z with hR
  have s1 : Summable fun z => u z ^ 2 := (hu.of_zero hu (fun z h _ => by simp [h])).summable
  have hD : ∀ h, D u h = 2 * Q - 2 * R h := by
    intro h
    have s2 : Summable fun z => u (act h z) ^ 2 :=
      ((hu.comp_act h).of_zero (hu.comp_act h) (fun z h _ => by simp [h])).summable
    have s3 : Summable fun z => u z * u (act h z) :=
      (hu.of_zero hu (fun z h _ => by simp [h])).summable
    have e2 : ∑' z, u (act h z) ^ 2 = Q := (actEquiv h).tsum_eq (fun w => u w ^ 2)
    have e3 : ∑' z, u z * u (act h z) = R h := by
      rw [← (actEquiv h⁻¹).tsum_eq (fun z => u z * u (act h z))]
      simp only [actEquiv_apply, act_act_inv, hR]
    unfold D
    have : ∀ z, (u z - u (act h z)) ^ 2 = u z ^ 2 + u (act h z) ^ 2 - 2 * (u z * u (act h z)) :=
      fun z => by ring
    simp_rw [this]
    rw [Summable.tsum_sub (s1.add s2) (s3.mul_left 2), Summable.tsum_add s1 s2,
      Summable.tsum_mul_left _ s3, e2, e3]
    ring
  -- `∑_h μ(h) R(h) = ⟨P u, u⟩`
  have hPR : ∑ h ∈ μ.support, μ h * R h = ∑' z, L μ (fun h => u (act h⁻¹ z)) * u z := by
    simp only [hR]
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun h _ =>
      ((hu.mul_left (fun z => μ h * u (act h⁻¹ z)))).summable.congr fun z => by ring)]
    refine tsum_congr fun z => ?_
    unfold L Finsupp.sum
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by ring
  -- `⟨u - P u, u⟩ = u(o) - ⟨μ^{*N} · δ_o, u⟩ ≤ u(o)`
  have hPu : ∀ z, u z - L μ (fun h => u (act h⁻¹ z)) = pn μ o 0 z - pn μ o N z := by
    intro z
    rw [P_uN, hu_def, uN, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have sPu : Summable fun z => L μ (fun h => u (act h⁻¹ z)) * u z :=
    (hu.mul_left _).summable
  have sQ : Summable fun z => u z * u z := (hu.mul_left _).summable
  have s0 : Summable fun z => pn μ o 0 z * u z := (hu.mul_left _).summable
  have sN : Summable fun z => pn μ o N z * u z := (hu.mul_left _).summable
  have hQP : Q - ∑' z, L μ (fun h => u (act h⁻¹ z)) * u z ≤ u o := by
    have hQ' : Q = ∑' z, u z * u z := tsum_congr fun z => sq (u z)
    rw [hQ', ← Summable.tsum_sub sQ sPu]
    have : ∀ z, u z * u z - L μ (fun h => u (act h⁻¹ z)) * u z =
        pn μ o 0 z * u z - pn μ o N z * u z := fun z => by
      rw [← sub_mul, ← sub_mul, hPu]
    simp_rw [this]
    rw [Summable.tsum_sub s0 sN]
    have h0 : ∑' z, pn μ o 0 z * u z = u o := by
      have : ∀ z, pn μ o 0 z * u z = if z = o then u z else 0 := fun z => by
        rw [pn_zero]
        by_cases hz : z = o
        · simp [hz]
        · simp [hz, Ne.symm hz]
      simp_rw [this]
      exact tsum_ite_eq o u
    have hN : 0 ≤ ∑' z, pn μ o N z * u z :=
      tsum_nonneg fun z => mul_nonneg (pn_nonneg hμ.1 o N z) (uN_nonneg hμ.1 o N z)
    linarith
  -- assemble
  have hmass : ∑ h ∈ μ.support, μ h = 1 := hμ.2
  have hE : E μ u = 2 * Q * ∑ h ∈ μ.support, μ h - 2 * ∑ h ∈ μ.support, μ h * R h := by
    unfold E Finsupp.sum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun h _ => by dsimp only; rw [hD]; ring
  rw [hE, hmass, hPR]
  linarith

/-! ## Transience -/
lemma hit_single (μ : FF →₀ ℝ) (n : ℕ) (y o : ℝ) : hit μ n y {o} = pn μ o n y := by
  unfold hit pn L
  refine Finsupp.sum_congr fun g _ => ?_
  simp only [Finset.mem_singleton, act_inv_eq_iff]
  split_ifs <;> ring

lemma hit_nonneg {μ : FF →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (n : ℕ) (y : ℝ) (A : Finset ℝ) :
    0 ≤ hit μ n y A :=
  Finset.sum_nonneg fun g _ => by
    dsimp only
    split_ifs
    · exact cpow_nonneg hμ0 n g
    · exact le_rfl

/-- Transience towards a single point. -/
theorem summable_hit_single (μ : FF →₀ ℝ) (hμ : IsProbability μ)
    (hnd : IsStrictlyNondegenerate μ) (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ IsDyadic y) (o : ℝ) :
    Summable (fun n => hit μ n y {o}) := by
  by_cases hex : ∃ g : FF, act g⁻¹ y = o
  · obtain ⟨g₀, hg₀⟩ := hex
    have ho : 0 < o ∧ o < 1 ∧ IsDyadic o := hg₀ ▸ act_dyadic g₀⁻¹ hy
    have hyo : act g₀ o = y := (act_inv_eq_iff g₀ o y).mp hg₀
    obtain ⟨C, hC, hH⟩ := hardy hμ.1 hnd ho
    obtain ⟨C₁, hC₁, hD⟩ := D_le_E hμ.1 (mem_closure_of_nd hnd g₀)
    refine summable_of_sum_range_le (c := max 1 (8 * C ^ 2 + 8 * C₁ * C))
      (fun n => hit_nonneg hμ.1 n y {o}) (fun N => ?_)
    simp_rw [hit_single]
    change uN μ o N y ≤ _
    set u := uN μ o N
    have hu : FS u := uN_FS μ o N
    have hE := E_uN_le hμ o N
    have hE0 : 0 ≤ E μ u := E_nonneg hμ.1 u
    have huo0 : 0 ≤ u o := uN_nonneg hμ.1 o N o
    have huy0 : 0 ≤ u y := uN_nonneg hμ.1 o N y
    have h1 : u o ^ 2 ≤ C * E μ u := hH u hu
    have huo : u o ≤ 2 * C := by
      by_contra hc
      push Not at hc
      nlinarith
    have h2 : (u o - u y) ^ 2 ≤ C₁ * E μ u := by
      have := term_le_D hu g₀ o
      rw [hyo] at this
      exact this.trans (hD u hu)
    have h3 : u y ^ 2 ≤ 8 * C ^ 2 + 8 * C₁ * C := by
      nlinarith [sq_nonneg (u y - 2 * u o), mul_le_mul_of_nonneg_left hE hC₁]
    rcases le_or_gt (u y) 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (by nlinarith : u y ≤ 8 * C ^ 2 + 8 * C₁ * C).trans (le_max_right _ _)
  · push Not at hex
    have h0 : ∀ n, hit μ n y {o} = 0 := by
      intro n
      unfold hit
      refine Finset.sum_eq_zero fun g _ => ?_
      simp [hex g]
    simp only [h0]
    exact summable_zero

/-- **Part T target.** Transience of the induced random walk on the dyadics of `(0,1)`. -/
theorem summable_hit (μ : FF →₀ ℝ) (hμ : IsProbability μ) (hnd : IsStrictlyNondegenerate μ)
    (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ IsDyadic y) (A : Finset ℝ) :
    Summable (fun n => hit μ n y A) := by
  have hdec : ∀ n, hit μ n y A = ∑ o ∈ A, hit μ n y {o} := by
    intro n
    unfold hit Finsupp.sum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Finset.mem_singleton]
    rw [Finset.sum_ite_eq]
  simp_rw [hdec]
  exact summable_sum fun o _ => summable_hit_single μ hμ hnd y hy o

end ThompsonAmenability.Kai.PartT
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part T: transience -/
alias summable_hit := ThompsonAmenability.Kai.PartT.summable_hit

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

/-! ## Integration against finitely supported weights -/

/-! ## Convolution powers -/

/-! ## The configuration cocycle and the bad set -/

/-! ## The laws `pdist` -/

/-! ## The limit law -/

end ThompsonAmenability.Kai.PartS
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part S: the limit law -/

end ThompsonAmenability.Kai
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai.PartL
open ThompsonAmenability.Kai

end ThompsonAmenability.Kai.PartL
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai
/-! ## Part L: the shift and the periodicity contradiction -/

end ThompsonAmenability.Kai
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai.PartL
open ThompsonAmenability.Kai

end ThompsonAmenability.Kai.PartL
end

section
open CannonFloydParry Filter Topology
namespace ThompsonAmenability.Kai

/-! ## Assembly -/

end ThompsonAmenability.Kai
end

end
end

section
section
namespace ThompsonWalk

/-- The development's convolution powers agree with powers in the monoid algebra. -/
theorem cpow_eq_coeff_pow (μ : CannonFloydParry.F →₀ ℝ) (n : ℕ) :
    ThompsonAmenability.Kai.cpow μ n = ((MonoidAlgebra.ofCoeff μ) ^ n).coeff := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
    simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single]
    rw [← ih]
    rfl

theorem summable_green_of_isStrictlyNondegenerate (μ : CannonFloydParry.F →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hnd : ThompsonAmenability.IsStrictlyNondegenerate μ)
    (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ CannonFloydParry.IsDyadic y) (A : Finset ℝ) :
    Summable fun n : ℕ => ((MonoidAlgebra.ofCoeff μ) ^ n).coeff.sum fun g w =>
      if CannonFloydParry.extend ((g⁻¹ : CannonFloydParry.F) : CannonFloydParry.UI ≃o CannonFloydParry.UI) y ∈ A
      then w else 0 := by
  have h := ThompsonAmenability.Kai.summable_hit μ hμ hnd y hy A
  refine h.congr fun n => ?_
  simp only [ThompsonAmenability.Kai.hit, cpow_eq_coeff_pow]
  rfl

end ThompsonWalk

end
end

section
open ThompsonWalk

theorem solution (μ : CannonFloydParry.F →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hnd : ThompsonAmenability.IsStrictlyNondegenerate μ)
    (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ CannonFloydParry.IsDyadic y) (A : Finset ℝ) :
    Summable fun n : ℕ => ((MonoidAlgebra.ofCoeff μ) ^ n).coeff.sum fun g w =>
      if CannonFloydParry.extend ((g⁻¹ : CannonFloydParry.F) : CannonFloydParry.UI ≃o CannonFloydParry.UI) y ∈ A
      then w else 0 := by
  apply ThompsonWalk.summable_green_of_isStrictlyNondegenerate <;> assumption

end
