-- Prove2me | solution 1 for PerturbedWF.eq_2_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-15T14:49:33.865318+00:00
-- url     : https://prove2.me/submissions/bb5d1fd0-7fd2-4381-9828-62f771174125

import Mathlib
import Definitions.Def_PerturbedWF_WClass

open PerturbedWF

namespace P2MHole01_64bc841c
theorem solution {ι : Type} [inst : Fintype ι] (C : Set (ι → ℝ)) (hC : IsConfigSpace C) (x y : ι → ℝ)
  (hx : x ∈ C) (hy : y ∈ C) : ∑ i, (x - y) i = 0 := by
  obtain ⟨_, ⟨c, _, hsum⟩⟩ := hC
  simp [sub_eq_add_neg, Finset.sum_add_distrib, hsum x hx, hsum y hy]
end P2MHole01_64bc841c

/-- Step 1 (zero-sum). Both configurations have total mass `c`, so `x - y` sums to `0`. -/
theorem cfg_zero_sum {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) (hC : IsConfigSpace C)
    (x y : ι → ℝ) (hx : x ∈ C) (hy : y ∈ C) : ∑ i, (x - y) i = 0 := by
  (first | exact P2MHole01_64bc841c.solution C hC x y hx hy | (apply P2MHole01_64bc841c.solution <;> assumption))

/-- The divergence of a flow `F` at a node `a`: the net inflow. The value of
`∑ i, ∑ j, F i j • (e_j − e_i)` at `a` is `∑ i, F i a − ∑ j, F a j`. -/
theorem flow_div_at {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) (a : ι) :
    (∑ i : ι, ∑ j : ι, F i j • ((Pi.single j (1 : ℝ) - Pi.single i (1 : ℝ)) : ι → ℝ)) a =
      ∑ i, F i a - ∑ j, F a j := by
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
  change ∑ x, ∑ x_1, F x x_1 * ((if a = x_1 then 1 else 0) - (if a = x then 1 else 0)) =
    ∑ i, F i a - ∑ j, F a j
  have S1 : (∑ x, ∑ x_1, F x x_1 * (if a = x_1 then 1 else 0)) = ∑ x, F x a := by
    congr
    funext x
    · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
  have S2 : (∑ x, ∑ x_1, F x x_1 * (if a = x then 1 else 0)) = ∑ x, F a x := by
    have h2 : (∑ x, ∑ x_1, F x x_1 * (if a = x then 1 else 0)) =
        ∑ x, (if a = x then 1 else 0) * (∑ x_1, F x x_1) := by
      congr
      funext x
      · simp only [Finset.sum_mul, Finset.mul_sum, mul_comm]
    rw [h2]
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
  calc
    _ = (∑ x, ∑ x_1, F x x_1 * (if a = x_1 then 1 else 0)) -
        (∑ x, ∑ x_1, F x x_1 * (if a = x then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ x, F x a) - (∑ x, F a x) := by rw [S1, S2]
    _ = ∑ i, F i a - ∑ j, F a j := by rfl

/-- Step 2 (flow existence). Every zero-sum vector is the divergence of a nonnegative flow. -/
theorem cfg_flow_exists {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ℝ)
    (h : ∑ i, z i = 0) :
    ∃ F : ι → ι → ℝ, (∀ i j, 0 ≤ F i j) ∧
      z = ∑ i, ∑ j, F i j • (Pi.single j (1 : ℝ) - Pi.single i (1 : ℝ)) := by
  set pos : ι → ℝ := fun i => max (z i) 0 with hpos
  set neg : ι → ℝ := fun i => max (-(z i)) 0 with hneg
  set M : ℝ := ∑ i, pos i with hM
  have hposnn : ∀ i, 0 ≤ pos i := by
    intro i; simp only [hpos]; exact le_max_right (z i) 0
  have hnegnn : ∀ i, 0 ≤ neg i := by
    intro i; simp only [hneg]; exact le_max_right (-(z i)) 0
  have hMnn : 0 ≤ M := by
    simp only [hM]; apply Finset.sum_nonneg; intro i _; exact hposnn i
  -- hz_decomp: z a = pos a - neg a for all a
  have hz_decomp : z = fun a => pos a - neg a := by
    ext a
    simp only [hpos, hneg]
    by_cases hz : z a ≤ 0
    · have h1 : max (z a) 0 = 0 := max_eq_right hz
      have h2 : max (-z a) 0 = -z a := by
        have h : 0 ≤ -z a := by linarith
        exact max_eq_left h
      rw [h1, h2]
      ring
    · have hz' : 0 < z a := by linarith
      have h1 : max (z a) 0 = z a := by
        have h : 0 ≤ z a := by linarith
        exact max_eq_left h
      have h2 : max (-z a) 0 = 0 := by
        have h : -z a ≤ 0 := by linarith
        exact max_eq_right h
      rw [h1, h2]
      ring
  -- neg i = pos i - z i for all i
  have hneg_eq : ∀ i, neg i = pos i - z i := by
    intro i
    simp only [hpos, hneg]
    by_cases hz : z i ≤ 0
    · have h1 : max (z i) 0 = 0 := max_eq_right hz
      have h2 : max (-z i) 0 = -z i := by
        have h : 0 ≤ -z i := by linarith
        exact max_eq_left h
      rw [h1, h2]
      ring
    · have hz' : 0 < z i := by linarith
      have h1 : max (z i) 0 = z i := by
        have h : 0 ≤ z i := by linarith
        exact max_eq_left h
      have h2 : max (-z i) 0 = 0 := by
        have h : -z i ≤ 0 := by linarith
        exact max_eq_right h
      rw [h1, h2]
      ring
  -- ∑ neg i = M (from zero-sum)
  have hM_neg : ∑ i, neg i = M := by
    rw [show (∑ i, neg i) = ∑ i, (pos i - z i) from by congr 1; funext i; exact hneg_eq i]
    rw [Finset.sum_sub_distrib, hM, h]
    ring
  -- Case split on M > 0
  by_cases hM0 : 0 < M
  · -- M > 0: F i j := neg i * pos j / M
    refine ⟨fun i j => neg i * pos j / M, ?_, ?_⟩
    · -- nonnegativity
      intro i j
      apply div_nonneg
      · exact mul_nonneg (hnegnn i) (hposnn j)
      · linarith
    -- z = divergence(F)
    · ext a
      have hMne0 : M ≠ 0 := ne_of_gt hM0
      have hsumpos : (∑ j, pos j) = M := hM.symm
      have hsumneg : (∑ i, neg i) = M := hM_neg
      have hinflow : (∑ i, neg i * pos a / M) = pos a := by
        have hc : (∑ i, neg i * pos a / M) = ∑ i, neg i * (pos a / M) := by
          congr 1; funext i; ring
        have hsumc : (∑ i, neg i * (pos a / M)) = (∑ i, neg i) * (pos a / M) := by
          simp only [Finset.sum_mul]
        rw [hc, hsumc, hsumneg]
        field_simp [hMne0]
      have houtflow : (∑ j, neg a * pos j / M) = neg a := by
        have hc : (∑ j, neg a * pos j / M) = ∑ j, (neg a / M) * pos j := by
          congr 1; funext j; ring
        have hsumc : (∑ j, (neg a / M) * pos j) = (neg a / M) * (∑ j, pos j) := by
          simp only [Finset.mul_sum]
        rw [hc, hsumc, hsumpos]
        field_simp [hMne0]
      rw [flow_div_at, hinflow, houtflow]
      rw [hz_decomp]
  · -- M = 0: z = 0, F = 0
    have hM0' : M = 0 := by
      apply le_antisymm
      · linarith
      · exact hMnn
    have hsum_pos0 : ∑ i, pos i = 0 := (hM.symm).trans hM0'
    have hsum_neg0 : ∑ i, neg i = 0 := hM_neg.trans hM0'
    have hpos_zero : pos = 0 := by
      ext i
      apply le_antisymm
      · have hs : pos i ≤ ∑ x, pos x := Finset.single_le_sum (fun i _ => hposnn i) (Finset.mem_univ i)
        rw [hsum_pos0] at hs
        exact hs
      · exact hposnn i
    have hneg_zero : neg = 0 := by
      ext i
      apply le_antisymm
      · have hs : neg i ≤ ∑ x, neg x := Finset.single_le_sum (fun i _ => hnegnn i) (Finset.mem_univ i)
        rw [hsum_neg0] at hs
        exact hs
      · exact hnegnn i
    have hz0 : z = 0 := by
      rw [hz_decomp, hpos_zero, hneg_zero]
      funext a
      simp
    refine ⟨0, ?_, ?_⟩
    · intro i j; simp
    · rw [hz0]
      simp

namespace P2MHole03_cac3ab8e
/-- `dot` is linear in the vector argument: `dot v (∑ i, f i) = ∑ i, dot v (f i)`. -/
lemma dot_sum {ι : Type} [inst : Fintype ι] (v : ι → ℝ) (f : ι → (ι → ℝ)) :
    dot v (∑ i, f i) = ∑ i, dot v (f i) := by
  simp [dot]
  rw [Finset.sum_congr rfl (fun k _ => Finset.mul_sum Finset.univ _ _)]
  rw [Finset.sum_comm]

/-- `dot` is homogeneous in the vector argument: `dot v (c • x) = c * dot v x`. -/
lemma dot_smul {ι : Type} [inst : Fintype ι] (v x : ι → ℝ) (c : ℝ) :
    dot v (c • x) = c * dot v x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => show v k * (c * x k) = c * (v k * x k) from by ring)]
  rw [← Finset.mul_sum]

/-- `dot` is additive in the vector argument: `dot v (x - y) = dot v x - dot v y`. -/
lemma dot_sub {ι : Type} [inst : Fintype ι] (v x y : ι → ℝ) :
    dot v (x - y) = dot v x - dot v y := by
  simp [dot]
  rw [Finset.sum_congr rfl (fun k _ => show v k * (x k - y k) = v k * x k - v k * y k from by ring)]
  rw [Finset.sum_sub_distrib]

/-- `dot v (e_i) = v i`, for the standard basis vector `e_i = Pi.single i 1`. -/
lemma dot_single {ι : Type} [inst : Fintype ι] [inst_1 : DecidableEq ι] (v : ι → ℝ) (i : ι) :
    dot v (Pi.single i 1) = v i := by
  simp [dot, Pi.single_apply]

/-- `dot v (a • (e_j - e_i)) = a * (v j - v i)` for the standard basis vectors. -/
lemma flow_dot {ι : Type} [inst : Fintype ι] [inst_1 : DecidableEq ι]
    (v : ι → ℝ) (F : ι → ι → ℝ) (i j : ι) :
    dot v (F i j • (Pi.single j 1 - Pi.single i 1)) = F i j * (v j - v i) := by
  rw [dot_smul v (Pi.single j 1 - Pi.single i 1) (F i j),
      dot_sub v (Pi.single j 1) (Pi.single i 1),
      dot_single v j, dot_single v i]

/-- Applying `dot v` to a flow decomposes it into the cost `∑ i, ∑ j, F i j * (v j - v i)`. -/
lemma dot_sum_flow {ι : Type} [inst : Fintype ι] [inst_1 : DecidableEq ι]
    (v : ι → ℝ) (F : ι → ι → ℝ) :
    dot v (∑ i, ∑ j, F i j • (Pi.single j 1 - Pi.single i 1)) =
      ∑ i, ∑ j, F i j * (v j - v i) := by
  refine (dot_sum v (fun i => ∑ j, F i j • (Pi.single j 1 - Pi.single i 1))).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  refine (dot_sum v (fun j => F i j • (Pi.single j 1 - Pi.single i 1))).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact flow_dot v F i j

theorem solution {ι : Type} [inst : Fintype ι] [inst_1 : DecidableEq ι] (v z : ι → ℝ) (F : ι → ι → ℝ)
  (h : z = ∑ i, ∑ j, F i j • (Pi.single j 1 - Pi.single i 1)) : dot v z = ∑ i, ∑ j, (v j - v i) * F i j := by
  rw [h]
  refine (dot_sum_flow v F).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm (F i j) (v j - v i)
end P2MHole03_cac3ab8e

/-- Step 3 (pairing). The pairing of `v` with a flow's net divergence is the sum of the
per-edge price differences. -/
theorem cfg_dot_divergence {ι : Type} [Fintype ι] [DecidableEq ι] (v z : ι → ℝ) (F : ι → ι → ℝ)
    (h : z = ∑ i, ∑ j, F i j • (Pi.single j (1 : ℝ) - Pi.single i (1 : ℝ))) :
    dot v z = ∑ i, ∑ j, (v j - v i) * F i j := by
  (first | exact P2MHole03_cac3ab8e.solution v z F h | (apply P2MHole03_cac3ab8e.solution <;> assumption))

namespace P2MHole04_b308af8d
theorem solution {ι : Type} [inst : Fintype ι] (d : ι → ι → ℝ) (v : ι → ℝ) (hv : v ∈ dualBall d)
  (hd : IsFinMetric d) (F : ι → ι → ℝ) (hF : ∀ (i j : ι), 0 ≤ F i j) :
  ∑ i, ∑ j, (v j - v i) * F i j ≤ ∑ i, ∑ j, d i j * F i j := by
  have hterm (i j : ι) : (v j - v i) * F i j ≤ d i j * F i j := by
    have hle : v j - v i ≤ d i j :=
      calc
        v j - v i ≤ |v j - v i| := le_abs_self _
        _ ≤ d j i := hv j i
        _ ≤ d i j := (hd.2.1 j i).le
    exact mul_le_mul_of_nonneg_right hle (hF i j)
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
end P2MHole04_b308af8d

/-- Step 4 (Lipschitz bound). For `v` in the dual ball and a nonnegative flow, the sum of the
price differences is bounded by the cost `∑ i j, d i j * F i j`. -/
theorem cfg_edge_bound {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (v : ι → ℝ) (hv : v ∈ dualBall d)
    (hd : IsFinMetric d) (F : ι → ι → ℝ) (hF : ∀ i j, 0 ≤ F i j) :
    ∑ i, ∑ j, (v j - v i) * F i j ≤ ∑ i, ∑ j, d i j * F i j := by
  (first | exact P2MHole04_b308af8d.solution d v hv hd F hF | (apply P2MHole04_b308af8d.solution <;> assumption))

/-- **Eq. (2.3)** (p.5, PDF p.6). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

For `v ∈ B*`, `⟨v, x − y⟩ ≤ ‖x − y‖` for all `x, y ∈ C`.

**Formalization Note.** `B*` is `dualBall d` (`|v_i − v_j| ≤ d(i, j)`), `‖·‖` the
transportation norm (2.1). -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (v : ι → ℝ)
    (hv : v ∈ dualBall d) (x y : ι → ℝ) (hx : x ∈ C) (hy : y ∈ C) :
    dot v (x - y) ≤ transNorm d (x - y) := by
  set S : Set ℝ := {c : ℝ | ∃ F : ι → ι → ℝ, (∀ i j, 0 ≤ F i j) ∧
      x - y = ∑ i, ∑ j, F i j • (Pi.single j (1 : ℝ) - Pi.single i (1 : ℝ)) ∧
      c = ∑ i, ∑ j, d i j * F i j} with hS
  have hsum : ∑ i, (x - y) i = 0 := cfg_zero_sum C hC x y hx hy
  obtain ⟨F0, hF0nn, hF0⟩ := cfg_flow_exists (x - y) hsum
  have hF0inS : (∑ i, ∑ j, d i j * F0 i j) ∈ S := ⟨F0, hF0nn, hF0, rfl⟩
  have hbound : dot v (x - y) ≤ sInf S :=
    le_csInf (Set.nonempty_of_mem hF0inS) (fun c hc => by
      obtain ⟨F, hFnn, hF, rfl⟩ := hc
      rw [cfg_dot_divergence v (x - y) F hF]
      exact cfg_edge_bound d v hv hd F hFnn)
  exact hbound
