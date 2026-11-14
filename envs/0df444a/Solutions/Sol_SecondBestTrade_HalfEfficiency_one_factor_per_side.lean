-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.one_factor_per_side
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:56.410195+00:00
-- url     : https://prove2.me/submissions/e5f915d0-d04c-42c3-aea2-f43e34a497b4

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

private theorem sumLocal {A : Type} [Fintype A] [DecidableEq A] {T : A → Type} [∀ a, Fintype (T a)]
    (w f : ∀ a, T a → ℝ) :
    (∑ v : ∀ a, T a, (∏ a, w a (v a)) * ∏ a, f a (v a)) =
      ∏ a, ∑ t, w a t * f a t := by
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun a t => w a t * f a t)).symm

private def coupling (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (a : Agent N) (t : Ty N a) (c : Bool) (s : Ty N a) : ℝ :=
  if c then if s = t then p a else 0 else N.mass a s - p a * eta a s

private theorem couplingNonneg (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hdom : ∀ a s, p a * eta a s ≤ N.mass a s)
    (a : Agent N) (t : Ty N a) (c : Bool) (s : Ty N a) : 0 ≤ coupling N eta p a t c s := by
  cases c <;> by_cases h : s = t <;> simp [coupling, h, hp, sub_nonneg.mpr (hdom _ _)]

private theorem couplingMarginal (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (hen : ∀ a, ∑ t, eta a t = 1) (a : Agent N) (s : Ty N a) :
    ∑ c : Bool, ∑ t, eta a t * coupling N eta p a t c s = N.mass a s := by
  simp [Fintype.sum_bool, coupling, mul_ite, ← Finset.sum_mul, hen]
  ring

private theorem couplingAccept (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (a : Agent N) (t : Ty N a) : ∑ s, coupling N eta p a t true s = p a := by simp [coupling]

private theorem couplingTotal (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (hen : ∀ a, ∑ t, eta a t = 1) (a : Agent N) (t : Ty N a) :
    ∑ c : Bool, ∑ s, coupling N eta p a t c s = 1 := by
  simp [Fintype.sum_bool, coupling, Finset.sum_sub_distrib, N.mass_sum, ← Finset.mul_sum, hen]

private theorem totalMarginal (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (hen : ∀ a, ∑ t, eta a t = 1) (s : Profile N) :
    (∑ c : Agent N → Bool, ∑ t : Profile N, (∏ a, eta a (t a)) *
        ∏ a, coupling N eta p a (t a) (c a) (s a)) = prior N s := by
  have inn (c : Agent N → Bool) := sumLocal eta (fun (a : Agent N) (t : Ty N a) => coupling N eta p a t (c a) (s a))
  simp_rw [inn]
  rw [← Fintype.prod_sum (fun (a : Agent N) (b : Bool) => ∑ t, eta a t * coupling N eta p a t b (s a))]
  simp only [couplingMarginal N eta p hen, prior]

private theorem acceptance (N : Market) (eta : ∀ a, Ty N a → ℝ) (p : Agent N → ℝ)
    (hen : ∀ a, ∑ t, eta a t = 1) (t : Profile N) (i : Fin N.nb) (j : Fin N.ns) :
    (∑ c : Agent N → Bool, ∑ s : Profile N,
      (∏ a, coupling N eta p a (t a) (c a) (s a)) *
        ((if c (.inl i) then (1 : ℝ) else 0) * (if c (.inr j) then (1 : ℝ) else 0))) =
      p (.inl i) * p (.inr j) := by
  classical
  let g := fun (a : Agent N) (b : Bool) => if a = .inl i ∨ a = .inr j then (if b then (1 : ℝ) else 0) else 1
  have prodg (c : Agent N → Bool) : (∏ a, g a (c a)) =
      ((if c (.inl i) then (1 : ℝ) else 0) * (if c (.inr j) then (1 : ℝ) else 0)) := by
    rw [Fintype.prod_sum_type]
    have bi : (∏ k, g (.inl k) (c (.inl k))) = g (.inl i) (c (.inl i)) := by
      apply Finset.prod_eq_single i <;> simp_all [g]
    have sj : (∏ k, g (.inr k) (c (.inr k))) = g (.inr j) (c (.inr j)) := by
      apply Finset.prod_eq_single j <;> simp_all [g]
    rw [bi,sj]
    simp [g]
  have inn (c : Agent N → Bool) := (Fintype.prod_sum (fun (a : Agent N) (s : Ty N a) => coupling N eta p a (t a) (c a) s)).symm
  simp_rw [← prodg, ← Finset.sum_mul, inn]
  rw [sumLocal (fun a b => ∑ s, coupling N eta p a (t a) b s) g]
  let h := fun (a : Agent N) => ∑ b : Bool, (∑ s, coupling N eta p a (t a) b s) * g a b
  have hh (a : Agent N) : h a = if a = .inl i ∨ a = .inr j then p a else 1 := by
    by_cases hsel : a = .inl i ∨ a = .inr j
    · simp [h,g,hsel,Fintype.sum_bool,couplingAccept]
    · simpa only [h,g,if_neg hsel,mul_one] using couplingTotal N eta p hen a (t a)
  change (∏ a, h a) = _
  simp_rw [hh]
  rw [Fintype.prod_sum_type]
  simp


private theorem weightedRetention (N : Market) (z : Dual N) (eta : ∀ a, Ty N a → ℝ)
    (p : Agent N → ℝ) (hp : ∀ a, 0 ≤ p a) (hdom : ∀ a s, p a * eta a s ≤ N.mass a s)
    (X : Finset (Trade N)) (hX : X ∈ N.family) (t s : Profile N) (c : Agent N → Bool) :
    let w := ∏ a, coupling N eta p a (t a) (c a) (s a)
    w * (∑ e ∈ X, ((if c (.inl (N.buyer e)) then (1 : ℝ) else 0) *
        (if c (.inr (N.seller e)) then (1 : ℝ) else 0)) * virtualGain N z t e) ≤ w * Hvirtual N z s := by
  classical
  intro w
  by_cases hw : w = 0
  · simp [hw]
  have agree (a : Agent N) (hc : c a = true) : s a = t a := by
    by_contra hne
    have hzero : coupling N eta p a (t a) (c a) (s a) = 0 := by simp [coupling,hc,hne]
    exact hw (Finset.prod_eq_zero (Finset.mem_univ a) hzero)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun a _ => couplingNonneg N eta p hp hdom a _ _ _))
  let Y := X.filter (fun e => c (.inl (N.buyer e)) = true ∧ c (.inr (N.seller e)) = true)
  have hy := N.downward X hX Y (Finset.filter_subset _ _)
  have eq : (∑ e ∈ X, ((if c (.inl (N.buyer e)) then (1 : ℝ) else 0) *
        (if c (.inr (N.seller e)) then (1 : ℝ) else 0)) * virtualGain N z t e) =
      ∑ e ∈ Y, virtualGain N z s e := by
    unfold Y
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    cases hb : c (.inl (N.buyer e)) <;> cases hs : c (.inr (N.seller e)) <;> simp [hb,hs]
    simp [virtualGain, agree _ hb, agree _ hs]
  rw [eq]
  exact Finset.le_sup' (fun X => ∑ e ∈ X, virtualGain N z s e) hy

private theorem tradeTwoSidedThinning (N : Market) (z : Dual N) (eta : ∀ a, Ty N a → ℝ)
    (hen : ∀ a, ∑ t, eta a t = 1) (hpos : ∀ a t, 0 ≤ eta a t)
    (pb ps : ℝ) (hpb : 0 ≤ pb) (hps : 0 ≤ ps)
    (hdom : ∀ a s, Sum.elim (fun _ => pb) (fun _ => ps) a * eta a s ≤ N.mass a s) :
    (pb * ps) * (∑ t : Profile N, (∏ a, eta a (t a)) * Hvirtual N z t) ≤ expect N (Hvirtual N z) := by
  classical
  let p : Agent N → ℝ := Sum.elim (fun _ => pb) (fun _ => ps)
  have hp (a : Agent N) : 0 ≤ p a := by cases a <;> assumption
  let w := fun (t : Profile N) (c : Agent N → Bool) (s : Profile N) => ∏ a, coupling N eta p a (t a) (c a) (s a)
  let rho := fun (t : Profile N) => ∏ a, eta a (t a)
  have hrho (t : Profile N) : 0 ≤ rho t := Finset.prod_nonneg (fun a _ => hpos a _)
  have step (t : Profile N) : (pb*ps) * Hvirtual N z t ≤
      ∑ c : Agent N → Bool, ∑ s : Profile N, w t c s * Hvirtual N z s := by
    obtain ⟨X,hX,he⟩ := Finset.exists_mem_eq_sup' N.family_nonempty (fun X => ∑ e ∈ X, virtualGain N z t e)
    change (pb*ps) * N.family.sup' N.family_nonempty (fun X => ∑ e ∈ X, virtualGain N z t e) ≤ _
    rw [he, Finset.mul_sum]
    let keep := fun (c : Agent N → Bool) e => (if c (.inl (N.buyer e)) then (1 : ℝ) else 0) *
        (if c (.inr (N.seller e)) then (1 : ℝ) else 0)
    calc
      _ = ∑ e ∈ X, (∑ c : Agent N → Bool, ∑ s : Profile N, w t c s * keep c e) * virtualGain N z t e := by
        apply Finset.sum_congr rfl
        intro e _
        rw [show (∑ c : Agent N → Bool, ∑ s : Profile N, w t c s * keep c e) = pb * ps from acceptance N eta p hen t (N.buyer e) (N.seller e)]
      _ = ∑ c : Agent N → Bool, ∑ s : Profile N, w t c s * (∑ e ∈ X, keep c e * virtualGain N z t e) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ ≤ _ := Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun s _ =>
        weightedRetention N z eta p hp hdom X hX t s c
  have endMarg (s : Profile N) :
      (∑ c : Agent N → Bool, ∑ t : Profile N, rho t * w t c s) = prior N s := totalMarginal N eta p hen s
  calc
    _ = ∑ t : Profile N, rho t * ((pb * ps) * Hvirtual N z t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => mul_left_comm _ _ _)
    _ ≤ ∑ t : Profile N, rho t * (∑ c : Agent N → Bool, ∑ s : Profile N, w t c s * Hvirtual N z s) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (step t) (hrho t))
    _ = _ := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (f := fun t s => rho t * w t _ s * Hvirtual N z s)]
      rw [Finset.sum_comm]
      unfold expect
      apply Finset.sum_congr rfl
      intro s _
      simp only [← Finset.sum_mul, endMarg]
theorem solution (N : Market) (z : Dual N) (hz : useful N z)
    (thetaB thetaS : ℝ) (hB : 0 ≤ thetaB) (hS : 0 ≤ thetaS) :
    conditionalSurplus N z thetaB thetaS ≤
      Real.exp (kappa (z.tau : ℝ) * (thetaB + thetaS)) * expect N (Hvirtual N z) := by
  classical
  let k := kappa (z.tau : ℝ)
  let θ : Agent N → ℝ := Sum.elim (fun _ => thetaB) (fun _ => thetaS)
  have hθ (a : Agent N) : 0 ≤ θ a := by cases a <;> assumption
  let eta := fun (a : Agent N) t => terminalMass N z a (θ a) t
  have hsum (a : Agent N) : ∑ t, eta a t = 1 := by
    simp only [eta,terminalMass]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,tradeTransitionRowSum,mul_one,N.mass_sum]
  have hnn (a : Agent N) (t : Ty N a) : 0 ≤ eta a t := Finset.sum_nonneg (fun s _ =>
      mul_nonneg (N.mass_pos a s).le (tradeTransitionNonnegative N z a (θ a) (hθ a) s t))
  let pb := (Real.exp (k * thetaB))⁻¹
  let ps := (Real.exp (k * thetaS))⁻¹
  have hdom (a : Agent N) (s : Ty N a) : Sum.elim (fun _ => pb) (fun _ => ps) a * eta a s ≤ N.mass a s := by
    have h := tradeDensityAtTime N z hz a s (θ a) (hθ a)
    cases a with
    | inl i =>
      change (Real.exp (k*thetaB))⁻¹ * eta (.inl i) s ≤ _
      rw [inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _),mul_comm (N.mass _ _)]
      exact h
    | inr j =>
      change (Real.exp (k*thetaS))⁻¹ * eta (.inr j) s ≤ _
      rw [inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _),mul_comm (N.mass _ _)]
      exact h
  have bound := tradeTwoSidedThinning N z eta hsum hnn pb ps
    (inv_nonneg.mpr (Real.exp_pos _).le) (inv_nonneg.mpr (Real.exp_pos _).le) hdom
  change pb * ps * conditionalSurplus N z thetaB thetaS ≤ _ at bound
  have id : pb * ps = (Real.exp (k * (thetaB + thetaS)))⁻¹ := by
    rw [mul_add,Real.exp_add, mul_inv]
  rw [id, inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _)] at bound
  simpa only [mul_comm (expect N (Hvirtual N z))] using bound
