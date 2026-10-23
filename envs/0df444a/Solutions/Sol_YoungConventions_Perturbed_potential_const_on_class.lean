-- Prove2me | solution 1 for YoungConventions.Perturbed.potential_const_on_class
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:49:34.78077+00:00
-- url     : https://prove2.me/submissions/f4b61614-82cc-48dd-8517-e12d1ce514b0

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset


namespace YoungConventions.Perturbed

theorem hasRes_unique_core {X : Type*} [Fintype X] [DecidableEq X]
    (P : ℝ → Matrix X X ℝ) (x y : X) (r r' : ℝ)
    (h : HasResistance P x y r) (h' : HasResistance P x y r') (hlt : r < r') : False := by
  obtain ⟨-, c, hc, hT⟩ := h
  obtain ⟨-, c', -, hT'⟩ := h'
  have hpow : Tendsto (fun ε : ℝ => ε ^ (r' - r)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (r' - r) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hprod := hpow.mul hT'
  rw [zero_mul] at hprod
  have heq : (fun ε : ℝ => ε ^ (r' - r) * (ε ^ (-r') * P ε x y)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ε ^ (-r) * P ε x y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← mul_assoc, ← Real.rpow_add hε]
    ring_nf
  have h2 := hprod.congr' heq
  have := tendsto_nhds_unique h2 hT
  linarith

theorem resistance_spec_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X) :
    (∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r') ∧
    ((∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y) ∧
    (IsEdge P x y → HasResistance P x y (resistance P x y)) ∧
    ((IsEdge P x y ∧ resistance P x y = 0) ↔ 0 < P0 x y) := by
  have huniq : ∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r' := by
    intro r r' h h'
    rcases lt_trichotomy r r' with hl | he | hg
    · exact (hasRes_unique_core P x y r r' h h' hl).elim
    · exact he
    · exact (hasRes_unique_core P x y r' r h' h hg).elim
  have hedge : (∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y := by
    intro hex
    obtain ⟨r, -, c, hc, hT⟩ := hP.order x y hex
    have hev := hT.eventually_const_lt hc
    filter_upwards [hev, self_mem_nhdsWithin] with ε h1 h2
    have hp : 0 < ε ^ (-r) := Real.rpow_pos_of_pos h2 _
    exact (mul_pos_iff_of_pos_left hp).mp h1
  have hres : IsEdge P x y → HasResistance P x y (resistance P x y) := by
    intro he
    have hex : ∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y := by
      obtain ⟨ε, h1, h2⟩ := (he.and (Ioc_mem_nhdsGT hP.pos)).exists
      exact ⟨ε, h2, h1⟩
    have hr := hP.order x y hex
    unfold resistance
    rw [dif_pos hr]
    exact Classical.choose_spec hr
  refine ⟨huniq, hedge, hres, ?_, ?_⟩
  · rintro ⟨he, h0⟩
    have h := hres he
    rw [h0] at h
    obtain ⟨-, c, hc, hT⟩ := h
    have hT2 : Tendsto (fun ε : ℝ => P ε x y) (𝓝[>] 0) (𝓝 c) := by
      refine hT.congr ?_
      intro ε
      simp
    have := tendsto_nhds_unique (hP.tendsto x y) hT2
    linarith
  · intro hpos
    have he : IsEdge P x y := (hP.tendsto x y).eventually_const_lt hpos
    refine ⟨he, ?_⟩
    have h0 : HasResistance P x y 0 := by
      refine ⟨le_rfl, P0 x y, hpos, ?_⟩
      refine (hP.tendsto x y).congr ?_
      intro ε
      simp
    exact huniq _ _ (hres he) h0


theorem resistance_nonneg_core {X : Type*} [Fintype X] [DecidableEq X]
    (P : ℝ → Matrix X X ℝ) (x y : X) : 0 ≤ resistance P x y := by
  unfold resistance
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact le_rfl

theorem reaches_rtg_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X) :
    ∀ n : ℕ, ∀ x y : X, 0 < (A ^ n) x y → Relation.ReflTransGen (fun a b => 0 < A a b) x y := by
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  have hpnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (pow_mem hA n)).1
  intro n
  induction n with
  | zero =>
    intro x y h
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hxy
    · rw [hxy]
    · exact absurd h (lt_irrefl 0)
  | succ n ih =>
    intro x y h
    rw [pow_succ, Matrix.mul_apply] at h
    by_contra hcon
    have : ∑ k, (A ^ n) x k * A k y ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      by_contra hk
      push Not at hk
      have h1 : 0 < (A ^ n) x k := by
        rcases lt_or_eq_of_le (hpnn n x k) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      have h2 : 0 < A k y := by
        rcases lt_or_eq_of_le (hnn k y) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      exact hcon ((ih x k h1).tail h2)
    linarith

theorem potential_step_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X)
    (hxy : 0 < P0 x y) : statePotential P y ≤ statePotential P x := by
  by_cases hxy' : x = y
  · rw [hxy']
  have hspec := (resistance_spec_core P0 hP0 P a hP x y).2.2.2.mpr hxy
  obtain ⟨hedge, hr0⟩ := hspec
  have key : ∀ (f : X → ℝ) (z : X), ∑ v ∈ univ.erase z, f v = ∑ v, (if v = z then 0 else f v) := by
    intro f z
    rw [← Finset.add_sum_erase univ _ (mem_univ z)]
    rw [if_pos rfl, zero_add]
    apply Finset.sum_congr rfl
    intro v hv
    rw [if_neg (Finset.ne_of_mem_erase hv)]
  unfold statePotential
  apply le_iInf₂
  intro T hT
  let T' : X → X := fun v => if v = x ∨ v = y then y else T v
  have hT'x : T' x = y := by simp [T']
  have hT'y : T' y = y := by simp [T']
  have hT'o : ∀ v, v ≠ x → v ≠ y → T' v = T v := by
    intro v h1 h2; simp [T', h1, h2]
  have hiter : ∀ n : ℕ, ∀ v, T^[n] v = x → ∃ m, T'^[m] v = y := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simp only [Function.iterate_zero, id_eq] at hv
      exact ⟨1, by simp [hv, hT'x]⟩
    | succ n ih =>
      intro v hv
      by_cases h1 : v = x
      · exact ⟨1, by simp [h1, hT'x]⟩
      by_cases h2 : v = y
      · exact ⟨0, by simp [h2]⟩
      rw [Function.iterate_succ_apply] at hv
      obtain ⟨m, hm⟩ := ih (T v) hv
      exact ⟨m + 1, by rw [Function.iterate_succ_apply, hT'o v h1 h2]; exact hm⟩
  have hTree : IsGTree P y T' := by
    refine ⟨⟨hT'y, fun v => ?_⟩, fun v hv => ?_⟩
    · obtain ⟨n, hn⟩ := hT.1.2 v
      exact hiter n v hn
    · by_cases h1 : v = x
      · rw [h1, hT'x]; exact hedge
      · rw [hT'o v h1 hv]; exact hT.2 v h1
  refine le_trans (iInf₂_le T' hTree) ?_
  rw [EReal.coe_le_coe_iff, key, key]
  apply Finset.sum_le_sum
  intro v _
  by_cases h2 : v = y
  · rw [if_pos h2]
    split_ifs
    · exact le_rfl
    · exact resistance_nonneg_core P _ _
  rw [if_neg h2]
  by_cases h1 : v = x
  · rw [if_pos h1, h1, hT'x, hr0]
  · rw [if_neg h1, hT'o v h1 h2]

theorem potential_rtg_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X)
    (h : Relation.ReflTransGen (fun a b => 0 < P0 a b) x y) :
    statePotential P y ≤ statePotential P x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (potential_step_core P0 hP0 P a hP _ _ hbc) ih

theorem potential_const_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (C : Finset X) (hC : C ∈ recurrentClasses P0) (x y : X) (hx : x ∈ C) (hy : y ∈ C) :
    statePotential P x = statePotential P y := by
  classical
  unfold recurrentClasses at hC
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hC
  unfold commClass at hx hy
  obtain ⟨-, ⟨n1, hzx⟩, ⟨n2, hxz⟩⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, ⟨n3, hzy⟩, ⟨n4, hyz⟩⟩ := Finset.mem_filter.mp hy
  have r1 := reaches_rtg_core P0 hP0 _ _ _ hzx
  have r2 := reaches_rtg_core P0 hP0 _ _ _ hxz
  have r3 := reaches_rtg_core P0 hP0 _ _ _ hzy
  have r4 := reaches_rtg_core P0 hP0 _ _ _ hyz
  apply le_antisymm
  · exact potential_rtg_core P0 hP0 P a hP _ _ (r4.trans r1)
  · exact potential_rtg_core P0 hP0 P a hP _ _ (r2.trans r3)

end YoungConventions.Perturbed

open YoungConventions.Perturbed


theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (C : Finset X) (hC : C ∈ recurrentClasses P0) (x y : X) (hx : x ∈ C) (hy : y ∈ C) :
    statePotential P x = statePotential P y := by
  exact potential_const_core P0 hP0 P a hP C hC x y hx hy
