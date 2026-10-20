-- Prove2me | solution 1 for Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.reduction
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:05.666388+00:00
-- url     : https://prove2.me/submissions/016cf6f7-6e2b-4f6b-b192-795e1c0f82c3

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_parallelogram

/-!
Reduction of a c₀ sum of blocks of dimension at most two: drop zero blocks, keep lines and
planes whose ball has more than four extreme points, and split every other plane (an `ℓ∞²`)
into two lines. The reduced c₀ sum is linearly isometric to the original one.
-/

universe u v

open Plasticity Filter Topology

namespace Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_reduction

open Classical

/-- The reduced condition on a block. -/
def Red (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] : Prop :=
  Module.finrank ℝ W = 1 ∨ (Module.finrank ℝ W = 2 ∧
    4 < (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).encard)

theorem encard_extremePoints_congr {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : W ≃ₗᵢ[ℝ] V) :
    (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).encard =
      (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard := by
  have h := image_extremePoints (𝕜 := ℝ) L (Metric.closedBall (0 : W) 1)
  rw [L.image_closedBall, map_zero] at h
  rw [← h, L.injective.encard_image]

/-- Block decomposition: a space of rank at most two is the maximum sum of two subspaces,
each zero or reduced. -/
theorem block_decomp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.rank ℝ V ≤ 2) :
    ∃ S : Bool → Submodule ℝ V,
      (∀ x : V, ∃ a ∈ S false, ∃ b ∈ S true, a + b = x) ∧
      (∀ a ∈ S false, ∀ b ∈ S true, ‖a + b‖ = max ‖a‖ ‖b‖) ∧
      (∀ k, S k = ⊥ ∨ Red (S k)) := by
  have hfin : FiniteDimensional ℝ V := Module.rank_lt_aleph0_iff.1
    (lt_of_le_of_lt hV Cardinal.ofNat_lt_aleph0)
  have hle : Module.finrank ℝ V ≤ 2 := Module.finrank_le_of_rank_le (n := 2) (by exact_mod_cast hV)
  -- the trivial decomposition `V = V ⊕ 0`
  have htriv : (Module.finrank ℝ V = 0 ∨ Red V) → ∃ S : Bool → Submodule ℝ V,
      (∀ x : V, ∃ a ∈ S false, ∃ b ∈ S true, a + b = x) ∧
      (∀ a ∈ S false, ∀ b ∈ S true, ‖a + b‖ = max ‖a‖ ‖b‖) ∧
      (∀ k, S k = ⊥ ∨ Red (S k)) := by
    intro hred
    refine ⟨fun k => if k then ⊥ else ⊤, fun x => ⟨x, by simp, 0, by simp, add_zero x⟩,
      fun a _ b hb => ?_, fun k => ?_⟩
    · simp only [if_true, Submodule.mem_bot] at hb
      rw [hb, add_zero, norm_zero, max_eq_left (norm_nonneg a)]
    · cases k
      · show (⊤ : Submodule ℝ V) = ⊥ ∨ Red (⊤ : Submodule ℝ V)
        rcases hred with h0 | hred
        · left
          rw [Module.finrank_zero_iff] at h0
          exact Subsingleton.elim _ _
        · right
          have L := LinearIsometryEquiv.ofTop V (⊤ : Submodule ℝ V) rfl
          unfold Red at hred ⊢
          rw [encard_extremePoints_congr L, finrank_top]
          exact hred
      · simp
  rcases Nat.lt_or_ge (Module.finrank ℝ V) 2 with hlt | hge
  · rcases (by omega : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 1) with h | h
    · exact htriv (Or.inl h)
    · exact htriv (Or.inr (Or.inl h))
  have h2 : Module.finrank ℝ V = 2 := le_antisymm hle hge
  rcases lt_or_ge 4 (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard with h4 | h4
  · exact htriv (Or.inr (Or.inr ⟨h2, h4⟩))
  -- a parallelogram: `V = ℝ a ⊕∞ ℝ b`
  obtain ⟨a, b, hab⟩ :=
    Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.parallelogram h2 h4
  have ha1 : ‖a‖ = 1 := by simpa using hab 1 0
  have hb1 : ‖b‖ = 1 := by simpa using hab 0 1
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha1
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb1
  have hli : LinearIndependent ℝ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have := hab s t
    rw [hst, norm_zero] at this
    have hs := le_max_left |s| |t|
    have ht := le_max_right |s| |t|
    exact ⟨abs_eq_zero.1 (le_antisymm (by linarith) (abs_nonneg s)),
      abs_eq_zero.1 (le_antisymm (by linarith) (abs_nonneg t))⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  refine ⟨fun k => if k then Submodule.span ℝ {b} else Submodule.span ℝ {a}, fun x => ?_,
    fun a' ha' b' hb' => ?_, fun k => ?_⟩
  · refine ⟨B.repr x 0 • a, ?_, B.repr x 1 • b, ?_, ?_⟩
    · simpa using Submodule.smul_mem _ (B.repr x 0) (Submodule.mem_span_singleton_self a)
    · simpa using Submodule.smul_mem _ (B.repr x 1) (Submodule.mem_span_singleton_self b)
    · have := B.sum_repr x
      rw [Fin.sum_univ_two] at this
      simpa [B] using this
  · simp only [Bool.false_eq_true, if_false, if_true, Submodule.mem_span_singleton] at ha' hb'
    obtain ⟨s, rfl⟩ := ha'
    obtain ⟨t, rfl⟩ := hb'
    rw [hab, norm_smul, norm_smul, ha1, hb1, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
  · right; left
    cases k
    · exact finrank_span_singleton ha0
    · exact finrank_span_singleton hb0

section C0

variable {ι : Type u} {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  (S : ∀ i, Bool → Submodule ℝ (E i))

/-- The reduced index set: the nonzero pieces of the blocks. -/
abbrev J : Type u := {p : ι × Bool // S p.1 p.2 ≠ ⊥}

/-- The reduced blocks. -/
abbrev G (j : J S) : Type v := ↥(S j.1.1 j.1.2)

variable {S}

/-- The piece of `y` at `(i, k)`, as an element of `E i` (zero when the piece is absent). -/
noncomputable def cmp (y : ∀ j : J S, G S j) (i : ι) (k : Bool) : E i :=
  if h : S i k ≠ ⊥ then ((y ⟨(i, k), h⟩ : S i k) : E i) else 0

theorem cmp_mem (y : ∀ j : J S, G S j) (i : ι) (k : Bool) : cmp y i k ∈ S i k := by
  unfold cmp
  split_ifs with h
  · exact (y ⟨(i, k), h⟩).2
  · exact zero_mem _

theorem norm_cmp_le (y : lp (G S) ⊤) (i : ι) (k : Bool) : ‖cmp (⇑y) i k‖ ≤ ‖y‖ := by
  unfold cmp
  split_ifs with h
  · calc ‖((y ⟨(i, k), h⟩ : S i k) : E i)‖ = ‖y ⟨(i, k), h⟩‖ := rfl
      _ ≤ ‖y‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero y _
  · simp

theorem cmp_add (y z : ∀ j : J S, G S j) (i : ι) (k : Bool) :
    cmp (y + z) i k = cmp y i k + cmp z i k := by
  unfold cmp
  split_ifs <;> simp

theorem cmp_smul (c : ℝ) (y : ∀ j : J S, G S j) (i : ι) (k : Bool) :
    cmp (c • y) i k = c • cmp y i k := by
  unfold cmp
  split_ifs <;> simp

/-- The sum of the pieces of `y` in each block. -/
noncomputable def psiFun (y : ∀ j : J S, G S j) : ∀ i, E i := fun i => cmp y i false + cmp y i true

variable (hmax : ∀ i, ∀ a ∈ S i false, ∀ b ∈ S i true, ‖a + b‖ = max ‖a‖ ‖b‖)
include hmax

theorem norm_psiFun (y : ∀ j : J S, G S j) (i : ι) :
    ‖psiFun y i‖ = max ‖cmp y i false‖ ‖cmp y i true‖ :=
  hmax i _ (cmp_mem y i false) _ (cmp_mem y i true)

theorem memℓp_psiFun (y : lp (G S) ⊤) : Memℓp (psiFun (⇑y)) ⊤ := by
  refine memℓp_infty ⟨‖y‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  dsimp only
  rw [norm_psiFun hmax]
  exact max_le (norm_cmp_le y i false) (norm_cmp_le y i true)

omit hmax in
theorem tendsto_cmp (y : c0Sum (G S)) (k : Bool) :
    Tendsto (fun i => ‖cmp (⇑(y : lp (G S) ⊤)) i k‖) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hy : Tendsto (fun j => ‖(y : lp (G S) ⊤) j‖) cofinite (𝓝 0) := y.2
  have hfin := Filter.eventually_cofinite.1 (hy.eventually_lt_const hε)
  refine (hfin.image (fun j => j.1.1)).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_norm] at hi
  by_cases h : S i k ≠ ⊥
  · refine ⟨⟨(i, k), h⟩, ?_, rfl⟩
    intro hlt
    apply hi
    unfold cmp
    rw [dif_pos h]
    exact hlt
  · exfalso
    apply hi
    unfold cmp
    rw [dif_neg h, norm_zero]
    exact hε

theorem mem_c0Sum_psiFun (y : c0Sum (G S)) :
    (⟨psiFun (⇑(y : lp (G S) ⊤)), memℓp_psiFun hmax y⟩ : lp E ⊤) ∈ c0Sum E := by
  show Tendsto (fun i => ‖psiFun (⇑(y : lp (G S) ⊤)) i‖) cofinite (𝓝 0)
  have h := (tendsto_cmp y false).add (tendsto_cmp y true)
  rw [add_zero] at h
  exact squeeze_zero (fun i => norm_nonneg _) (fun i => norm_add_le _ _) h

/-- The linear map from the reduced c₀ sum to the original one. -/
noncomputable def psi : c0Sum (G S) →ₗ[ℝ] c0Sum E where
  toFun y := ⟨⟨psiFun (⇑(y : lp (G S) ⊤)), memℓp_psiFun hmax y⟩, mem_c0Sum_psiFun hmax y⟩
  map_add' y z := by
    apply Subtype.ext
    apply lp.ext
    funext i
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, psiFun, cmp_add]
    abel
  map_smul' c y := by
    apply Subtype.ext
    apply lp.ext
    funext i
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, psiFun, cmp_smul,
      RingHom.id_apply, smul_add]

theorem psi_apply (y : c0Sum (G S)) (i : ι) :
    ((psi hmax y : c0Sum E) : lp E ⊤) i = psiFun (⇑(y : lp (G S) ⊤)) i := rfl

theorem norm_psi (y : c0Sum (G S)) : ‖psi hmax y‖ = ‖y‖ := by
  apply le_antisymm
  · rw [Submodule.coe_norm]
    refine lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_
    rw [psi_apply, norm_psiFun hmax]
    exact max_le (norm_cmp_le _ i false) (norm_cmp_le _ i true)
  · rw [Submodule.coe_norm]
    refine lp.norm_le_of_forall_le (norm_nonneg _) fun j => ?_
    obtain ⟨⟨i, k⟩, h⟩ := j
    have e : ‖(y : lp (G S) ⊤) ⟨(i, k), h⟩‖ = ‖cmp (⇑(y : lp (G S) ⊤)) i k‖ := by
      unfold cmp
      rw [dif_pos h]
      rfl
    rw [e]
    calc ‖cmp (⇑(y : lp (G S) ⊤)) i k‖
        ≤ max ‖cmp (⇑(y : lp (G S) ⊤)) i false‖ ‖cmp (⇑(y : lp (G S) ⊤)) i true‖ := by
          cases k
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = ‖((psi hmax y : c0Sum E) : lp E ⊤) i‖ := by rw [psi_apply, norm_psiFun hmax]
      _ ≤ ‖(psi hmax y : lp E ⊤)‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

omit hmax in
theorem finite_preimage (i : ι) : Finite ((fun j : J S => j.1.1) ⁻¹' {i}) := by
  refine Finite.of_injective (fun j : ((fun j : J S => j.1.1) ⁻¹' {i}) => j.1.1.2) ?_
  rintro ⟨⟨⟨i₁, k₁⟩, h₁⟩, hj₁⟩ ⟨⟨⟨i₂, k₂⟩, h₂⟩, hj₂⟩ hk
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj₁ hj₂
  simp only at hk
  subst hj₁ hj₂ hk
  rfl

theorem psi_surjective (hspan : ∀ i, ∀ x : E i, ∃ a ∈ S i false, ∃ b ∈ S i true, a + b = x) :
    Function.Surjective (psi hmax) := by
  intro x
  choose a ha b hb hab using fun i => hspan i ((x : lp E ⊤) i)
  set piece : ∀ i, Bool → E i := fun i k => cond k (b i) (a i) with hpiece
  have piece_mem : ∀ i k, piece i k ∈ S i k := by
    intro i k
    cases k
    · exact ha i
    · exact hb i
  have piece_le : ∀ i k, ‖piece i k‖ ≤ ‖(x : lp E ⊤) i‖ := by
    intro i k
    rw [← hab i, hmax i _ (ha i) _ (hb i)]
    cases k
    · exact le_max_left _ _
    · exact le_max_right _ _
  set yf : ∀ j : J S, G S j := fun j => ⟨piece j.1.1 j.1.2, piece_mem _ _⟩ with hyf
  have hyℓ : Memℓp yf ⊤ := by
    refine memℓp_infty ⟨‖x‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (piece_le _ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
  have hyc : (⟨yf, hyℓ⟩ : lp (G S) ⊤) ∈ c0Sum (G S) := by
    show Tendsto (fun j => ‖yf j‖) cofinite (𝓝 0)
    have hx : Tendsto (fun i => ‖(x : lp E ⊤) i‖) cofinite (𝓝 0) := x.2
    have hπ : Tendsto (fun j : J S => j.1.1) cofinite cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton finite_preimage
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => piece_le _ _) (hx.comp hπ)
  refine ⟨⟨⟨yf, hyℓ⟩, hyc⟩, ?_⟩
  apply Subtype.ext
  apply lp.ext
  funext i
  show cmp yf i false + cmp yf i true = (x : lp E ⊤) i
  have hc : ∀ k, cmp yf i k = piece i k := by
    intro k
    unfold cmp
    split_ifs with h
    · rfl
    · have hm := piece_mem i k
      rw [not_not.1 h, Submodule.mem_bot] at hm
      exact hm.symm
  rw [hc, hc]
  exact hab i

end C0

end Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_reduction

open Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_reduction in
theorem solution {ι : Type u} (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) :
    ∃ (J : Type u) (G : J → Type v) (_ : ∀ j, NormedAddCommGroup (G j))
      (_ : ∀ j, NormedSpace ℝ (G j)),
      (∀ j, Module.finrank ℝ (G j) = 1 ∨ (Module.finrank ℝ (G j) = 2 ∧
        4 < (Set.extremePoints ℝ (Metric.closedBall (0 : G j) 1)).encard)) ∧
      Nonempty (c0Sum G ≃ₗᵢ[ℝ] c0Sum E) := by
  choose S hspan hmax hred using fun i => block_decomp (hE i)
  refine ⟨J S, G S, inferInstance, inferInstance, fun j => ?_,
    ⟨LinearIsometryEquiv.ofSurjective ⟨psi hmax, norm_psi hmax⟩ (psi_surjective hmax hspan)⟩⟩
  rcases hred j.1.1 j.1.2 with h | h
  · exact absurd h j.2
  · exact h
