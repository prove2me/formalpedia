-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.prior_density
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:55.414677+00:00
-- url     : https://prove2.me/submissions/45c6457c-e23b-4520-ad8f-8585863475a1

import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators Matrix.Norms.Operator
open SecondBestTrade.HalfEfficiency

noncomputable section

private theorem tradeGeneratorOffDiagonal (N : Market) (z : Dual N) (a : Agent N)
    {t s : Ty N a} (h : t ≠ s) : 0 ≤ generator N z a t s := by
  simp only [generator, if_neg h]
  exact div_nonneg (z.flow a s (some t)).2 (mul_nonneg (by positivity) (N.mass_pos a t).le)

private theorem tradeGeneratorRowSum (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) :
    ∑ s, generator N z a t s = 0 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t)]
  let R := fun s : Ty N a => (z.flow a s (some t) : ℝ) / ((1 + (z.tau : ℝ)) * N.mass a t)
  have he : (∑ s ∈ Finset.univ.erase t, generator N z a t s) = ∑ s ∈ Finset.univ.erase t, R s := by
    apply Finset.sum_congr rfl
    intro s hs
    simp [generator, Ne.symm (Finset.ne_of_mem_erase hs), R]
  rw [he]
  change (∑ s ∈ Finset.univ.erase t, R s) + _ = _
  simp only [generator, if_pos rfl, R, add_neg_cancel]

private theorem tradeResolventInvertible (N : Market) (z : Dual N) (a : Agent N) :
    IsUnit (1 - generator N z a) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  apply det_ne_zero_of_sum_row_lt_diag
  intro t
  have hsum : (∑ s ∈ Finset.univ.erase t, generator N z a t s) = - generator N z a t t := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ t), tradeGeneratorRowSum, zero_sub]
  have hn : 0 ≤ - generator N z a t t := hsum ▸ Finset.sum_nonneg (fun s hs =>
    tradeGeneratorOffDiagonal N z a (Ne.symm (Finset.ne_of_mem_erase hs)))
  have each (s) (hs : s ∈ Finset.univ.erase t) :
      ‖(1 - generator N z a) t s‖ = generator N z a t s := by
    have h := Ne.symm (Finset.ne_of_mem_erase hs)
    simp [Matrix.sub_apply, Matrix.one_apply_ne h, Real.norm_eq_abs,
      abs_of_nonneg (tradeGeneratorOffDiagonal N z a h)]
  rw [Finset.sum_congr rfl each, hsum]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - generator N z a t t)]
  linarith

private theorem tradeVirtualGenerator (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) :
    virtual N z a t e = ∑ s, (1 - generator N z a) t s * coord N a s e := by
  classical
  let R := fun s : Ty N a => (z.flow a s (some t) : ℝ) / ((1 + (z.tau : ℝ)) * N.mass a t)
  have scaled : (∑ s, (z.flow a s (some t) : ℝ) * (coord N a s e - coord N a t e)) /
      ((1 + (z.tau : ℝ)) * N.mass a t) = ∑ s, R s * (coord N a s e - coord N a t e) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [R]
    ring
  rw [virtual, scaled, ← Finset.sum_erase_add _ _ (Finset.mem_univ t)]
  simp only [sub_self, mul_zero, add_zero]
  rw [← Finset.sum_erase_add _ (fun s => (1 - generator N z a) t s * coord N a s e) (Finset.mem_univ t)]
  have hdiag : generator N z a t t = -(∑ s ∈ Finset.univ.erase t, R s) := by simp [generator, R]
  have hoff (s) (hs : s ∈ Finset.univ.erase t) : (1 - generator N z a) t s * coord N a s e =
      -(R s * coord N a s e) := by
    have h := Ne.symm (Finset.ne_of_mem_erase hs)
    rw [Matrix.sub_apply, Matrix.one_apply_ne h]
    simp [generator, h, R]
  rw [Finset.sum_congr rfl hoff, Matrix.sub_apply, Matrix.one_apply_eq, hdiag]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

private theorem tradeSemigroup (N : Market) (z : Dual N) (a : Agent N) (s t : ℝ) :
    transition N z a (s + t) = transition N z a s * transition N z a t := by
  unfold transition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

private theorem tradeTransitionContinuous (N : Market) (z : Dual N) (a : Agent N) :
    Continuous (fun t => transition N z a t) := by
  exact (differentiable_exp_smul_const ℝ (generator N z a)).continuous

private theorem tradeResolventRecovery (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) :
    ∑ s, resolvent N z a t s * virtual N z a s e = coord N a t e := by
  let V : Matrix (Ty N a) (Trade N) ℝ := coord N a
  let Q := generator N z a
  have h := Matrix.nonsing_inv_mul_cancel_left (1-Q) V
    ((Matrix.isUnit_iff_isUnit_det _).mp (tradeResolventInvertible N z a))
  have hv (s) : virtual N z a s e = (((1-Q) * V : Matrix (Ty N a) (Trade N) ℝ)) s e := tradeVirtualGenerator N z a s e
  simp_rw [hv]
  exact congrFun (congrFun h t) e

private theorem tradePowNonnegative {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S ℝ)
    (h : ∀ i j, 0 ≤ A i j) (n : ℕ) (i j : S) : 0 ≤ (A ^ n) i j := by
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply]; split <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (h k j)

private theorem tradeExpNonnegative {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S ℝ)
    (h : ∀ i j, 0 ≤ A i j) (i j : S) : 0 ≤ NormedSpace.exp A i j := by
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j
  apply le_of_le_of_eq _ hs.tsum_eq
  apply tsum_nonneg
  intro n
  change 0 ≤ ((n.factorial : ℝ)⁻¹) * (A ^ n) i j
  exact mul_nonneg (by positivity) (tradePowNonnegative A h n i j)

private theorem tradeExpScalar {S : Type} [Fintype S] [DecidableEq S] (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix S S ℝ)) = Real.exp c • 1 := by
  have id (x : ℝ) : x • (1 : Matrix S S ℝ) = Matrix.diagonal (fun _ => x) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  rw [id, Matrix.exp_diagonal, id]
  congr 1
  funext i
  rw [Pi.coe_exp]
  change NormedSpace.exp c = Real.exp c
  rw [Real.exp_eq_exp_ℝ]

private theorem tradeTransitionNonnegative (N : Market) (z : Dual N) (a : Agent N)
    (θ : ℝ) (hθ : 0 ≤ θ) (i j : Ty N a) : 0 ≤ transition N z a θ i j := by
  classical
  let Q := generator N z a
  let C := ∑ s : Ty N a, |Q s s|
  let B := θ • (Q + C • (1 : Matrix (Ty N a) (Ty N a) ℝ))
  have hb (s t : Ty N a) : 0 ≤ B s t := by
    change 0 ≤ θ * (Q s t + C * (1 : Matrix (Ty N a) (Ty N a) ℝ) s t)
    apply mul_nonneg hθ
    by_cases he : s = t
    · subst t
      rw [Matrix.one_apply_eq, mul_one]
      have hle : |Q s s| ≤ C := Finset.single_le_sum (fun t _ => abs_nonneg (Q t t)) (Finset.mem_univ s)
      linarith [neg_abs_le (Q s s)]
    · simpa [Matrix.one_apply_ne he] using tradeGeneratorOffDiagonal N z a he
  have split : θ • Q = B + (-(θ*C)) • 1 := by
    dsimp [B]
    simp [smul_add, smul_smul]
  have ec : Commute B ((-(θ*C)) • 1) := (Commute.one_right B).smul_right _
  change 0 ≤ NormedSpace.exp (θ • Q) i j
  rw [split, Matrix.exp_add_of_commute _ _ ec, tradeExpScalar, Matrix.mul_smul, mul_one]
  exact mul_nonneg (Real.exp_pos _).le (tradeExpNonnegative B hb i j)

set_option maxHeartbeats 2000000 in
private theorem tradeTransitionRowSum (N : Market) (z : Dual N) (a : Agent N) (θ : ℝ) (i : Ty N a) :
    ∑ j, transition N z a θ i j = 1 := by
  let Q := θ • generator N z a
  let oneVec : Ty N a → ℝ := fun _ => 1
  have qone : Q.mulVec oneVec = 0 := by
    funext s
    simpa [Q, Matrix.mulVec, dotProduct, oneVec, ← Finset.mul_sum] using
      congrArg (fun x => θ * x) (tradeGeneratorRowSum N z a s)
  have pow (n : ℕ) : (Q ^ n.succ).mulVec oneVec = 0 := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, qone, Matrix.mulVec_zero]
  have terms (n : ℕ) :
      (∑ j, ((n.factorial : ℝ)⁻¹ • Q ^ n) i j) = if n = 0 then (1 : ℝ) else 0 := by
    cases n with
    | zero => simp [Matrix.one_apply]
    | succ n =>
      have eq := congrFun (pow n) i
      simp only [Matrix.mulVec, dotProduct, oneVec, mul_one, Pi.zero_apply] at eq
      rw [if_neg (Nat.succ_ne_zero _)]
      simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, eq, mul_zero]
  have hs (j : Ty N a) := Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Q) i) j
  have hall := hasSum_sum (s := Finset.univ) (a := fun j => (NormedSpace.exp Q) i j) (f := fun (j : Ty N a) (n : ℕ) => (((n.factorial : ℝ)⁻¹ • Q ^ n) i j))
      (fun j _ => hs j)
  simp_rw [terms] at hall
  change (∑ j, NormedSpace.exp Q i j) = 1
  rw [← hall.tsum_eq]
  simp

open MeasureTheory Set Filter
open scoped Topology

private theorem tradeTransitionLeOne (N : Market) (z : Dual N) (a : Agent N)
    {θ : ℝ} (hθ : 0 ≤ θ) (i j : Ty N a) : transition N z a θ i j ≤ 1 := by
  rw [← tradeTransitionRowSum N z a θ i]
  exact Finset.single_le_sum (fun k _ => tradeTransitionNonnegative N z a θ hθ i k) (Finset.mem_univ j)

private theorem tradeEntryContinuous (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
    Continuous (fun θ => transition N z a θ i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (tradeTransitionContinuous N z a))

private theorem tradeClockIntegrable (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * transition N z a x i j) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact ((Real.continuous_exp.comp continuous_id.neg).mul (tradeEntryContinuous N z a i j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hn := tradeTransitionNonnegative N z a x hx.le i j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hn)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (tradeTransitionLeOne N z a hx.le i j)

private theorem tradeClockLimit (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
    Tendsto (fun x : ℝ => Real.exp (-x) * transition N z a x i j) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.exp_pos _).le (tradeTransitionNonnegative N z a x hx i j)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_le_of_le_one_right (Real.exp_pos _).le (tradeTransitionLeOne N z a hx i j)

private theorem tradeResolventIntegral (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
    resolvent N z a i j = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * transition N z a x i j := by
  classical
  let Q := generator N z a
  let A : Matrix (Ty N a) (Ty N a) ℝ := 1 - Q
  let I : Matrix (Ty N a) (Ty N a) ℝ := fun i j => ∫ x in Ioi (0 : ℝ), Real.exp (-x) * transition N z a x i j
  have prod : A * I = 1 := by
    ext u v
    let f := fun x : ℝ => Real.exp (-x) * transition N z a x u v
    let fp := fun x : ℝ => -(∑ k, A u k * (Real.exp (-x) * transition N z a x k v))
    have der (x : ℝ) : HasDerivAt f (fp x) x := by
      have hex := hasDerivAt_exp_smul_const' Q x
      have he := hasDerivAt_pi.mp (hasDerivAt_pi.mp hex u) v
      have h := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).mul he
      apply h.congr_deriv
      dsimp [fp,A]
      simp only [Matrix.sub_apply, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib,
        Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        neg_sub, mul_neg, mul_one, ← Finset.mul_sum]
      change -Real.exp (-x) * transition N z a x u v + Real.exp (-x) *
          (∑ k, Q u k * transition N z a x k v) = _
      rw [Finset.mul_sum]
      have es : (∑ k, Real.exp (-x) * (Q u k * transition N z a x k v)) =
          ∑ k, Q u k * (Real.exp (-x) * transition N z a x k v) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [es]
      ring
    have int (k : Ty N a) := (tradeClockIntegrable N z a k v).const_mul (A u k)
    have fint : IntegrableOn fp (Ioi 0) := (integrable_finsetSum Finset.univ (fun k _ => int k)).neg
    have id := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => der x) fint (tradeClockLimit N z a u v)
    have start : f 0 = (1 : Matrix (Ty N a) (Ty N a) ℝ) u v := by simp [f,transition]
    rw [start, zero_sub] at id
    simp only [fp, integral_neg] at id
    have swap := integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ
      (f := fun (k : Ty N a) (x : ℝ) => A u k * (Real.exp (-x) * transition N z a x k v)) (fun k _ => int k)
    rw [swap] at id
    simp only [integral_const_mul, neg_inj] at id
    exact id
  have hi : A⁻¹ * (A * I) = I := Matrix.nonsing_inv_mul_cancel_left A I
    ((Matrix.isUnit_iff_isUnit_det _).mp (tradeResolventInvertible N z a))
  rw [prod, mul_one] at hi
  exact congrFun (congrFun hi i) j
private theorem tradeMassDrift (N : Market) (z : Dual N) (hz : useful N z) (a : Agent N) (t : Ty N a) :
    (∑ s, N.mass a s * generator N z a s t) ≤ kappa (z.tau : ℝ) * N.mass a t := by
  classical
  let D := 1 + (z.tau : ℝ)
  have hd : 0 < D := by dsimp [D]; positivity
  have off (s) (hs : s ∈ Finset.univ.erase t) : N.mass a s * generator N z a s t =
      (z.flow a t (some s) : ℝ) / D := by
    simp only [generator, if_neg (Finset.ne_of_mem_erase hs)]
    dsimp [D]
    field_simp [(N.mass_pos a s).ne']
  have diag : N.mass a t * generator N z a t t =
      -(∑ s ∈ Finset.univ.erase t, (z.flow a s (some t) : ℝ) / D) := by
    simp only [generator, if_pos rfl, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    dsimp [D]
    field_simp [(N.mass_pos a t).ne']
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t), Finset.sum_congr rfl off, diag,
    ← Finset.sum_div, ← Finset.sum_div, Finset.sum_erase_eq_sub (Finset.mem_univ t),
    Finset.sum_erase_eq_sub (Finset.mem_univ t)]
  change ((∑ s, (z.flow a t (some s) : ℝ)) - _) / D + -((inflow N z a t - _) / D) ≤ _
  have out := hz a t
  unfold outflow at out
  rw [Fintype.sum_option] at out
  change _ ≤ (z.tau : ℝ) / D * N.mass a t
  field_simp [hd.ne']
  nlinarith [(z.flow a t none).2]

private theorem tradeDensityAtTime (N : Market) (z : Dual N) (hz : useful N z) (a : Agent N) (t : Ty N a)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    terminalMass N z a θ t ≤ Real.exp (kappa (z.tau : ℝ) * θ) * N.mass a t := by
  classical
  let Q := generator N z a
  let k := kappa (z.tau : ℝ)
  let p := fun x => terminalMass N z a x t
  let d := fun x : ℝ => ∑ j, (∑ i, N.mass a i * Q i j) * transition N z a x j t
  have dp (x : ℝ) : HasDerivAt p (d x) x := by
    have hex := hasDerivAt_exp_smul_const' Q x
    have entry (i) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hex i) t
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (entry i).const_mul (N.mass a i))
    apply h.congr_deriv
    dsimp [d]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have bound (x : ℝ) (hx : 0 ≤ x) : d x ≤ k * p x := by
    dsimp [d,p,terminalMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (tradeMassDrift N z hz a j) (tradeTransitionNonnegative N z a x hx j t)
  let f := fun x : ℝ => Real.exp (-k*x) * p x
  let f' := fun x : ℝ => Real.exp (-k*x) * (d x - k*p x)
  have deriv (x : ℝ) : HasDerivAt f (f' x) x := by
    have he := (Real.hasDerivAt_exp (-k*x)).comp x ((hasDerivAt_id x).const_mul (-k))
    apply (he.mul (dp x)).congr_deriv
    dsimp [f']
    ring
  have anti : AntitoneOn f (Ici (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _) ((fun x => (deriv x).continuousAt) |> continuous_iff_continuousAt.mpr |>.continuousOn) (fun x _ => (deriv x).hasDerivWithinAt)
    intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (bound x (interior_subset hx)))
  have h := anti (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hθ) hθ
  have p0 : p 0 = N.mass a t := by simp [p, terminalMass, transition, Matrix.one_apply, mul_ite]
  change Real.exp (-k * θ) * p θ ≤ Real.exp (-k * 0) * p 0 at h
  rw [mul_zero, Real.exp_zero, one_mul, p0, neg_mul, Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)] at h
  simpa only [mul_comm (N.mass a t)] using h

theorem solution (N : Market) (z : Dual N) (hz : useful N z) :
    (∀ theta : ℝ, 0 ≤ theta → ∀ a t,
      terminalMass N z a theta t ≤ Real.exp (kappa (z.tau : ℝ) * theta) * N.mass a t) ∧
    (∀ a t, (∑ s, N.mass a s * resolvent N z a s t) ≤
      (1 + (z.tau : ℝ)) * N.mass a t) := by
  classical
  refine ⟨fun θ hθ a t => tradeDensityAtTime N z hz a t θ hθ, ?_⟩
  intro a t
  let k := kappa (z.tau : ℝ)
  have hd : 0 < 1 + (z.tau : ℝ) := by positivity
  have hk : k - 1 < 0 := sub_neg.mpr ((div_lt_one hd).mpr (by linarith))
  have hi (s : Ty N a) := (tradeClockIntegrable N z a s t).const_mul (N.mass a s)
  have lo : IntegrableOn (fun x => Real.exp (-x) * terminalMass N z a x t) (Ioi 0) := by
    simpa only [IntegrableOn, terminalMass, Finset.mul_sum, mul_left_comm] using (integrable_finsetSum Finset.univ (fun s _ => hi s))
  have up := (integrableOn_exp_mul_Ioi hk 0).mul_const (N.mass a t)
  calc
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * terminalMass N z a x t := by
      simp_rw [tradeResolventIntegral N z a]
      have swap := integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ
        (f := fun (s : Ty N a) (x : ℝ) => N.mass a s * (Real.exp (-x) * transition N z a x s t)) (fun s _ => hi s)
      simp only [integral_const_mul] at swap
      rw [← swap]
      congr 1
      funext x
      simp [terminalMass, Finset.mul_sum, mul_left_comm]
    _ ≤ ∫ x in Ioi (0 : ℝ), Real.exp ((k-1)*x) * N.mass a t := by
      apply integral_mono_ae lo up
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      have h := mul_le_mul_of_nonneg_left (tradeDensityAtTime N z hz a t x hx.le) (Real.exp_pos (-x)).le
      rw [← mul_assoc, ← Real.exp_add] at h
      convert h using 2
      dsimp [k]
      ring_nf
    _ = _ := by
      rw [integral_mul_const, integral_exp_mul_Ioi hk]
      dsimp [k,kappa]
      simp only [mul_zero, Real.exp_zero]
      field_simp
      <;> ring
