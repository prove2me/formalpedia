-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.markov_recovery
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:57.336869+00:00
-- url     : https://prove2.me/submissions/a0ef5214-011b-4ae6-b70e-20dcf53f990c

import Definitions.Def_SecondBestTrade_HalfEfficiency_Recovery

open scoped BigOperators NNReal ENNReal Matrix.Norms.Operator
open MeasureTheory Set Topology SecondBestTrade.HalfEfficiency

noncomputable section



theorem tradeGeneratorOffDiagonal (N : Market) (z : Dual N) (a : Agent N)
    {t s : Ty N a} (h : t ≠ s) : 0 ≤ generator N z a t s := by
  simp only [generator, if_neg h]
  exact div_nonneg (z.flow a s (some t)).2 (mul_nonneg (by positivity) (N.mass_pos a t).le)

theorem tradeGeneratorRowSum (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) :
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

theorem tradeResolventInvertible (N : Market) (z : Dual N) (a : Agent N) :
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

theorem tradeVirtualGenerator (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) :
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

theorem tradeSemigroup (N : Market) (z : Dual N) (a : Agent N) (s t : ℝ) :
    transition N z a (s + t) = transition N z a s * transition N z a t := by
  unfold transition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

theorem tradeTransitionContinuous (N : Market) (z : Dual N) (a : Agent N) :
    Continuous (fun t => transition N z a t) := by
  exact (differentiable_exp_smul_const ℝ (generator N z a)).continuous

theorem tradeResolventRecovery (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) :
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

theorem tradeTransitionNonnegative (N : Market) (z : Dual N) (a : Agent N)
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
theorem tradeTransitionRowSum (N : Market) (z : Dual N) (a : Agent N) (θ : ℝ) (i : Ty N a) :
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

theorem tradeClockIntegrable (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
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

theorem tradeResolventIntegral (N : Market) (z : Dual N) (a : Agent N) (i j : Ty N a) :
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



/-- For finite state spaces, the compactness of cylinders lets Carathéodory
extend consistent finite-coordinate laws, including arbitrary index sets. -/
theorem tradePathExtension {ι S : Type} [Fintype S] [MeasurableSpace S]
    (P : ∀ J : Finset ι, Measure (J → S)) (hp : IsProjectiveMeasureFamily (α := fun _ : ι => S) P) :
    ∃ μ : Measure (ι → S), ∀ (J : Finset ι) (B : Set (J → S)), MeasurableSet B →
      μ (cylinder J B) = P J B := by
  classical
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have clopen {s : Set (ι → S)} (hs : s ∈ measurableCylinders (fun _ : ι => S)) : IsClopen s := by
    obtain ⟨J,B,_,rfl⟩ := (mem_measurableCylinders s).mp hs
    exact ⟨(isClosed_discrete B).preimage J.continuous_restrict,
      (isOpen_discrete B).preimage J.continuous_restrict⟩
  let c := projectiveFamilyContent hp
  have sub : c.IsSigmaSubadditive := by
    intro f hf hf'
    obtain ⟨F,hcover⟩ := (clopen hf').1.isCompact.elim_finite_subcover f (fun i => (clopen (hf i)).2) (Subset.rfl)
    have eq : (⋃ i, f i) = ⋃ i ∈ F, f i := Subset.antisymm hcover (by
      intro x hx
      obtain ⟨i,_,hi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion_of_mem i hi)
    rw [eq]
    exact (addContent_biUnion_le (m := c) isSetRing_measurableCylinders (fun i _ => hf i)).trans (ENNReal.sum_le_tsum _)
  have gen : MeasurableSpace.pi = MeasurableSpace.generateFrom (measurableCylinders (fun _ : ι => S)) :=
    generateFrom_measurableCylinders.symm
  refine ⟨c.measure isSetSemiring_measurableCylinders gen.le sub,fun J B hB => ?_⟩
  rw [c.measure_eq isSetSemiring_measurableCylinders gen sub ((mem_measurableCylinders _).mpr ⟨J,B,hB,rfl⟩)]
  exact projectiveFamilyContent_cylinder hp hB



namespace TradeChain

variable {S : Type} [Fintype S] [DecidableEq S]
abbrev Time := ℝ≥0

def kernel (T : Time → Matrix S S ℝ) (nn : ∀ t i j, 0 ≤ T t i j)
    (row : ∀ t i, ∑ j, T t i j = 1) (t : Time) (i : S) : PMF S :=
  PMF.ofFintype (fun j => ENNReal.ofReal (T t i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => nn t i j),row,ENNReal.ofReal_one])

theorem kernel_comp (T : Time → Matrix S S ℝ) (nn : ∀ t i j, 0 ≤ T t i j)
    (row : ∀ t i, ∑ j, T t i j = 1) (sg : ∀ t u, T (t+u) = T t * T u)
    (t u : Time) (i : S) :
    ((kernel T nn row t i).bind (kernel T nn row u)) = kernel T nn row (t+u) i := by
  ext j
  simp only [PMF.bind_apply,tsum_fintype,kernel,PMF.ofFintype_apply,sg,Matrix.mul_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (nn t i k) (nn u k j))]
  simp only [ENNReal.ofReal_mul (nn _ _ _)]

/-- Fill the requested times in chronological order, sampling only the coordinates
visible in the observation function. -/
def scan {B : Type} (K : Time → S → PMF S) (keep : Time → Prop) [DecidablePred keep]
    (p : Time) (s : S) (v : Time → S) : List Time → ((Time → S) → B) → PMF B
  | [], f => PMF.pure (f v)
  | t :: ts, f => (K (t-p) s).bind fun j =>
      scan K keep t j (if keep t then Function.update v t j else v) ts f

private theorem scanMap {B C : Type} (K : Time → S → PMF S) (keep : Time → Prop) [DecidablePred keep]
    (p : Time) (s : S) (v : Time → S) (ts : List Time) (f : (Time → S) → B) (g : B → C) :
    (scan K keep p s v ts f).map g = scan K keep p s v ts (g ∘ f) := by
  induction ts generalizing p s v with
  | nil => exact PMF.pure_map _ _
  | cons a as ih =>
    simp only [scan,PMF.map_bind]
    congr 1
    funext j
    exact ih _ _ _

private theorem scanExt {B : Type} (K : Time → S → PMF S) (ks kt : Time → Prop)
    [DecidablePred ks] [DecidablePred kt] (J : Finset Time) (p : Time) (s : S)
    (v w : Time → S) (ts : List Time) (f : (Time → S) → B)
    (agree : ∀ t ∈ J, v t = w t) (same : ∀ t ∈ J, ks t ↔ kt t)
    (localF : ∀ v w : Time → S, (∀ t ∈ J, v t = w t) → f v = f w) :
    scan K ks p s v ts f = scan K kt p s w ts f := by
  classical
  induction ts generalizing p s v w with
  | nil => exact congrArg PMF.pure (localF v w agree)
  | cons t ts ih =>
    simp only [scan]
    congr 1
    funext j
    apply ih
    intro u hu
    by_cases eq : u = t
    · subst u
      by_cases hk : ks t
      · simp [hk,(same t hu).mp hk]
      · have hk' : ¬ kt t := fun h => hk ((same t hu).mpr h)
        simp only [if_neg hk,if_neg hk',agree t hu]
    · split <;> split <;> simpa only [Function.update_of_ne eq] using agree u hu

private theorem skip {B : Type} (K : Time → S → PMF S)
    (comp : ∀ t u i, (K t i).bind (K u) = K (t+u) i)
    (keep : Time → Prop) [DecidablePred keep] (p t : Time) (hp : p ≤ t) (s : S)
    (v : Time → S) (ts : List Time) (hs : ∀ u ∈ ts, t ≤ u) (f : (Time → S) → B) :
    (K (t-p) s).bind (fun j => scan K keep t j v ts f) = scan K keep p s v ts f := by
  cases ts with
  | nil => exact PMF.bind_const _ _
  | cons u us =>
    simp only [scan]
    rw [← PMF.bind_bind,comp]
    have sum : t - p + (u - t) = u - p := by
      rw [add_comm,tsub_add_tsub_cancel (hs u (by simp)) hp]
    rw [sum]

private theorem scanFilter {B : Type} (K : Time → S → PMF S)
    (comp : ∀ t u i, (K t i).bind (K u) = K (t+u) i)
    (keep : Time → Prop) [DecidablePred keep] (p : Time) (s : S) (v : Time → S)
    (ts : List Time) (ordered : ts.Pairwise (· ≤ ·)) (after : ∀ t ∈ ts, p ≤ t) (f : (Time → S) → B) :
    scan K keep p s v ts f = scan K keep p s v (ts.filter keep) f := by
  induction ts generalizing p s v with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨ht,hs⟩ := List.pairwise_cons.mp ordered
    by_cases hk : keep t
    · simp only [List.filter_cons,decide_eq_true hk,if_true,scan,hk]
      congr 1
      funext i
      simpa only [if_pos hk] using ih t i (Function.update v t i) hs ht
    · simp only [List.filter_cons,decide_eq_false hk,if_false,scan,hk]
      calc
        _ = scan K keep p s v ts f := skip K comp keep p t (after t (by simp)) s v ts ht f
        _ = _ := ih _ _ _ hs (fun u hu => after u (by simp [hu]))

def law (K : Time → S → PMF S) (s : S) (J : Finset Time) : PMF (J → S) :=
  scan K (fun _ => True) 0 s (fun _ => s) J.sort (fun v => J.restrict v)

theorem lawProject (K : Time → S → PMF S) (comp : ∀ t u i, (K t i).bind (K u) = K (t+u) i)
    (s : S) (I J : Finset Time) (h : J ⊆ I) :
    (law K s I).map (Finset.restrict₂ (π := fun _ : Time => S) h) = law K s J := by
  classical
  let obs := fun v : Time → S => J.restrict v
  let keep := fun t : Time => t ∈ J
  have localObs (v w : Time → S) (he : ∀ t ∈ J, v t = w t) : obs v = obs w :=
    funext (fun i => he i i.2)
  have ext (ts : List Time) : scan K (fun _ => True) 0 s (fun _ => s) ts obs =
      scan K keep 0 s (fun _ => s) ts obs :=
    scanExt K _ keep J 0 s _ _ ts obs (fun _ _ => rfl) (fun _ h => ⟨fun _ => h,fun _ => trivial⟩) localObs
  have filt : I.sort.filter keep = J.sort := by
    apply List.Pairwise.eq_of_mem_iff ((I.sortedLT_sort.pairwise).filter _) J.sortedLT_sort.pairwise
    intro t
    simp only [List.mem_filter,Finset.mem_sort,decide_eq_true_eq,keep]
    exact ⟨And.right,fun ht => ⟨h ht,ht⟩⟩
  unfold law
  rw [scanMap]
  change scan K (fun _ => True) 0 s (fun _ => s) I.sort obs = scan K (fun _ => True) 0 s (fun _ => s) J.sort obs
  calc
    _ = _ := ext (I.sort (· ≤ ·))
    _ = scan K keep 0 s (fun _ => s) ((I.sort (· ≤ ·)).filter keep) obs :=
      scanFilter K comp keep _ _ _ (I.sort (· ≤ ·)) (I.pairwise_sort _) (fun t _ => t.2) _
    _ = scan K keep 0 s (fun _ => s) (J.sort (· ≤ ·)) obs := by rw [filt]
    _ = _ := (ext (J.sort (· ≤ ·))).symm


private theorem duplicate {B : Type} (K : Time → S → PMF S) (zero : ∀ i, K 0 i = PMF.pure i)
    (p t : Time) (s : S) (v : Time → S) (ts : List Time) (f : (Time → S) → B) :
    scan K (fun _ => True) p s v (t::t::ts) f = scan K (fun _ => True) p s v (t::ts) f := by
  simp only [scan,if_true,tsub_self,zero,PMF.pure_bind,Function.update_idem]

private theorem canonical {B : Type} (K : Time → S → PMF S) (zero : ∀ i, K 0 i = PMF.pure i)
    (p : Time) (s : S) (v : Time → S) (ts : List Time) (order : ts.Pairwise (· ≤ ·))
    (f : (Time → S) → B) :
    scan K (fun _ => True) p s v ts f = scan K (fun _ => True) p s v ts.toFinset.sort f := by
  induction ts generalizing p s v with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨ht,ho⟩ := List.pairwise_cons.mp order
    by_cases h : t ∈ ts
    · cases ts with
      | nil => simp at h
      | cons u us =>
        have tu : t = u := by
          rcases List.mem_cons.mp h with h|h
          · exact h
          · exact le_antisymm (ht u (by simp)) ((List.pairwise_cons.mp ho).1 t h)
        subst u
        rw [duplicate K zero]
        have eq : (t::t::us).toFinset = (t::us).toFinset := by simp
        rw [eq]
        exact ih p s v ho
    · have hnot : t ∉ ts.toFinset := by simpa using h
      rw [List.toFinset_cons,Finset.sort_insert (· ≤ ·) (fun u hu => ht u (by simpa using hu)) hnot]
      simp only [scan,if_true]
      congr 1
      funext j
      exact ih _ _ _ ho

private def wordWeight (K : Time → S → PMF S) : ∀ (n : ℕ),
    (Fin n → Time) → (Fin n → S) → Time → S → ℝ≥0∞
  | 0, _,_,_,_ => 1
  | n+1,t,y,p,s => K (t 0-p) s (y 0) * wordWeight K n (fun i => t i.succ) (fun i => y i.succ) (t 0) (y 0)

private theorem scanWord (K : Time → S → PMF S) (zero : ∀ i, K 0 i = PMF.pure i)
    (n : ℕ) (t : Fin n → Time) (y : Fin n → S) (p : Time) (s : S) (v : Time → S)
    (mono : Monotone t) :
    scan K (fun _ => True) p s v (List.ofFn t) (fun w i => w (t i)) y = wordWeight K n t y p s := by
  induction n generalizing p s v with
  | zero =>
    have he : (fun i => v (t i)) = y := Subsingleton.elim _ _
    simp [scan,wordWeight,he]
  | succ n ih =>
    let tail := fun i : Fin n => t i.succ
    let ys := fun i : Fin n => y i.succ
    have mt : Monotone tail := fun _ _ h => mono (Fin.succ_le_succ_iff.mpr h)
    have expression (j : S) :
        scan K (fun _ => True) (t 0) j (Function.update v (t 0) j) (List.ofFn tail)
          (fun w i => w (t i)) y =
          if j = y 0 then wordWeight K n tail ys (t 0) j else 0 := by
      let w := Function.update v (t 0) j
      let f := fun (a : Time → S) (i : Fin (n+1)) => a (t i)
      let g := fun (a : Time → S) (i : Fin n) => a (tail i)
      have headConstant : ∀ (q : Time → S), q (t 0) = j → f q = Fin.cons j (g q) := by
        intro q hq
        funext i
        refine Fin.cases hq (fun i => rfl) i
      -- A zero-duration transition at the start of the tail also preserves j.
      have split : (scan K (fun _ => True) (t 0) j w (List.ofFn tail) f) =
          (scan K (fun _ => True) (t 0) j w (List.ofFn tail) g).map (Fin.cons j) := by
        rw [scanMap]
        have extObs : ∀ (us : List Time), us.Pairwise (· ≤ ·) → (∀ u ∈ us, t 0 ≤ u) →
            ∀ (p' : Time) (s' : S) (v' : Time → S), t 0 ≤ p' → v' (t 0) = j →
            (p' = t 0 → s' = j) → (∀ u ∈ us, p' ≤ u) →
            scan K (fun _ => True) p' s' v' us f =
              scan K (fun _ => True) p' s' v' us (Fin.cons j ∘ g) := by
          intro us order after
          induction us with
          | nil =>
            intro p' s' v' hp hv he future
            exact congrArg PMF.pure (headConstant _ hv)
          | cons u us ih =>
            intro p' s' v' hp hv he future
            obtain ⟨hi,hs⟩ := List.pairwise_cons.mp order
            by_cases eq : u = t 0
            · subst u
              have ep : p' = t 0 := le_antisymm (future _ (by simp)) hp
              subst p'
              have es := he rfl
              subst s'
              simp only [scan,if_true,tsub_self,zero,PMF.pure_bind]
              exact ih hs (fun u hu => after u (by simp [hu])) _ _ _ le_rfl (by simp) (fun _ => rfl) hi
            · simp only [scan,if_true]
              congr 1
              funext j'
              apply ih hs (fun u hu => after u (by simp [hu])) _ _ _ (after u (by simp))
                (by simpa only [Function.update_of_ne (Ne.symm eq)] using hv) (fun h => (eq h).elim) hi
        apply extObs _ mt.sortedLE_ofFn.pairwise (fun u hu => ?_) _ _ _ le_rfl (by simp [w]) (fun _ => rfl) (fun u hu => ?_) <;>
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
        all_goals exact mono (Fin.zero_le _)
      rw [show scan K (fun _ => True) (t 0) j (Function.update v (t 0) j) (List.ofFn tail)
        (fun w i => w (t i)) = _ from split,PMF.map_apply,tsum_fintype]
      by_cases he : j = y 0
      · subst j
        have iff (u : Fin n → S) : y = Fin.cons (y 0) u ↔ u = ys := by
          constructor
          · intro e
            funext i
            exact (congrFun e i.succ).symm
          · rintro rfl
            exact (Fin.cons_self_tail y).symm
        simp only [iff,if_pos rfl,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        exact ih tail ys (t 0) (y 0) w mt
      · have no (u : Fin n → S) : ¬ y = Fin.cons j u := fun e => he (congrFun e 0).symm
        simp [he,no]
    simp only [List.ofFn_succ,scan,if_true,PMF.bind_apply,tsum_fintype,wordWeight]
    change (∑ j, K (t 0-p) s j * scan K (fun _ => True) (t 0) j (Function.update v (t 0) j)
      (List.ofFn tail) (fun w i => w (t i)) y) = _
    simp only [expression,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl

private theorem wordProduct (K : Time → S → PMF S) (n : ℕ)
    (t : Fin (n+1) → Time) (y : Fin (n+1) → S) (p : Time) (s : S) :
    wordWeight K (n+1) t y p s = K (t 0 - p) s (y 0) *
      ∏ i : Fin n, K (t i.succ - t i.castSucc) (y i.castSucc) (y i.succ) := by
  induction n generalizing p s with
  | zero => simp [wordWeight]
  | succ n ih =>
    change K (t 0 - p) s (y 0) * wordWeight K (n+1) (fun i => t i.succ) (fun i => y i.succ) (t 0) (y 0) = _
    rw [ih, Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one,Fin.succ_castSucc, mul_assoc]

theorem lawObserve (K : Time → S → PMF S) (zero : ∀ i, K 0 i = PMF.pure i)
    (s : S) (n : ℕ) (t : Fin (n+1) → Time) (y : Fin (n+1) → S) (mono : Monotone t) (start : t 0 = 0) :
    let J := (List.ofFn t).toFinset
    let iof := fun i : Fin (n+1) => (⟨t i, List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩ : J)
    ((law K s J).map (fun z i => z (iof i))) y =
      (if y 0 = s then 1 else 0) * ∏ i : Fin n, K (t i.succ - t i.castSucc) (y i.castSucc) (y i.succ) := by
  dsimp only
  unfold law
  rw [scanMap]
  change scan K (fun _ => True) 0 s (fun _ => s) (List.ofFn t).toFinset.sort (fun w i => w (t i)) y = _
  rw [← canonical K zero 0 s (fun _ => s) (List.ofFn t) mono.sortedLE_ofFn.pairwise (fun w i => w (t i)),
    scanWord K zero _ _ _ _ _ _ mono,wordProduct K n]
  simp only [start,tsub_self,zero,PMF.pure_apply]
  by_cases e : y 0 = s <;> simp only [e,if_pos,if_neg,not_false_eq_true]

end TradeChain


private theorem chainExists (N : Market) (z : Dual N) (a : Agent N) (s : Ty N a) :
    letI : MeasurableSpace (Ty N a) := ⊤
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℝ≥0 → Ω → Ty N a),
      IsProbabilityMeasure P ∧ LambdaCoalescent.Rates.IsRateChain P (generator N z a) s X := by
  classical
  letI : MeasurableSpace (Ty N a) := ⊤
  letI : MeasurableSingletonClass (Ty N a) := ⟨fun _ => trivial⟩
  let T := fun t : ℝ≥0 => transition N z a (t : ℝ)
  let nn := fun (t : ℝ≥0) => tradeTransitionNonnegative N z a t t.2
  let row := fun (t : ℝ≥0) => tradeTransitionRowSum N z a t
  let K := TradeChain.kernel T nn row
  have zero (i : Ty N a) : K 0 i = PMF.pure i := by
    ext j
    simp only [K,TradeChain.kernel,PMF.ofFintype_apply,T,transition,NNReal.coe_zero,zero_smul,NormedSpace.exp_zero,
      Matrix.one_apply, PMF.pure_apply]
    by_cases e : i = j <;> simp [e,eq_comm]
  have comp := TradeChain.kernel_comp T nn row (fun t u => tradeSemigroup N z a t u)
  let law := TradeChain.law K s
  let P := fun J : Finset ℝ≥0 => (law J).toMeasure
  have proj : IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => Ty N a) P := by
    intro I J h
    change (law J).toMeasure = (law I).toMeasure.map _
    rw [PMF.toMeasure_map (Finset.restrict₂ (π := fun _ : ℝ≥0 => Ty N a) h) (law I) (Finset.measurable_restrict₂ h), show (law I).map (Finset.restrict₂ (π := fun _ : ℝ≥0 => Ty N a) h) = law J from TradeChain.lawProject K comp s I J h]
  obtain ⟨μ,hu⟩ := tradePathExtension P proj
  have univ : μ Set.univ = 1 := by
    have h := hu (∅ : Finset ℝ≥0) Set.univ MeasurableSet.univ
    simpa only [cylinder_univ,P,measure_univ] using h
  refine ⟨ℝ≥0 → Ty N a,MeasurableSpace.pi,μ,fun t w => w t,⟨univ⟩,fun t => measurable_pi_apply t,?_⟩
  intro n t h0 hm y
  let J := (List.ofFn t).toFinset
  let ix (i : Fin (n+1)) : J := ⟨t i,List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩
  let eval := fun (v : J → Ty N a) (i : Fin (n+1)) => v (ix i)
  have em : Measurable eval := measurable_pi_lambda _ (fun i => measurable_pi_apply (ix i))
  have singleton : MeasurableSet ({y} : Set (Fin (n+1) → Ty N a)) := measurableSet_singleton _
  have ev : {w : ℝ≥0 → Ty N a | ∀ i, w (t i) = y i} = cylinder J (eval ⁻¹' {y}) := by
    ext w
    exact ⟨fun h => funext h,fun h i => congrFun h i⟩
  have he := hu J (eval ⁻¹' {y}) (em singleton)
  have fm := (law J).toMeasure_map_apply eval {y} em singleton
  have word := TradeChain.lawObserve K zero s n t y hm h0
  rw [measureReal_def,ev,he]
  change ((law J).toMeasure (eval ⁻¹' {y})).toReal = _
  rw [← fm,PMF.toMeasure_apply_singleton _ _ singleton]
  change ((law J).map eval y).toReal = _
  rw [show (law J).map eval y = _ from word]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_prod,K,TradeChain.kernel,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (nn _ _ _),T,transition]
  simp only [apply_ite ENNReal.toReal,ENNReal.toReal_one,ENNReal.toReal_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [NNReal.coe_sub (hm (Fin.castSucc_le_succ i))]
  apply ENNReal.toReal_ofReal
  exact tradeTransitionNonnegative N z a _ (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hm (Fin.castSucc_le_succ i)))) _ _

theorem solution (N : Market) (z : Dual N) (_hz : useful N z) :
    ∀ a : Agent N,
      (∀ t e, virtual N z a t e = ∑ s,
        (1 - generator N z a) t s * coord N a s e) ∧
      recoveryProperties (generator N z a) (coord N a) (virtual N z a) := by
  classical
  intro a
  refine ⟨tradeVirtualGenerator N z a,tradeResolventInvertible N z a,tradeClockIntegrable N z a,
    tradeResolventIntegral N z a,fun θ hθ => ⟨by simpa only [transition,Nat.cast_smul_eq_nsmul] using tradeTransitionNonnegative N z a (θ : ℝ) (Nat.cast_nonneg θ),by simpa only [transition,Nat.cast_smul_eq_nsmul] using tradeTransitionRowSum N z a (θ : ℝ)⟩,
    by simp,fun θ η _ _ => by simpa only [transition,← Nat.cast_add,Nat.cast_smul_eq_nsmul] using tradeSemigroup N z a (θ : ℝ) (η : ℝ),tradeTransitionContinuous N z a,chainExists N z a,
    ?_,?_,tradeResolventRecovery N z a,?_,?_⟩
  · intro i j
    change 0 ≤ resolvent N z a i j
    rw [tradeResolventIntegral]
    apply setIntegral_nonneg measurableSet_Ioi
    intro θ hθ
    exact mul_nonneg (Real.exp_pos _).le (tradeTransitionNonnegative N z a θ (le_of_lt hθ) i j)
  · intro i
    change ∑ j, resolvent N z a i j = 1
    simp_rw [tradeResolventIntegral]
    rw [← integral_finsetSum Finset.univ (fun j _ => tradeClockIntegrable N z a i j)]
    simp_rw [← Finset.mul_sum,tradeTransitionRowSum,mul_one]
    exact integral_exp_neg_Ioi_zero
  · intro i e
    change IntegrableOn (fun θ => Real.exp (-θ) * ∑ j, transition N z a θ i j * virtual N z a j e) (Ioi 0)
    simp_rw [Finset.mul_sum,← mul_assoc]
    exact integrable_finsetSum _ (fun j _ => (tradeClockIntegrable N z a i j).mul_const _)
  · intro i e
    change (∫ θ in Ioi (0 : ℝ), Real.exp (-θ) * ∑ j, transition N z a θ i j * virtual N z a j e) = _
    simp_rw [Finset.mul_sum,← mul_assoc]
    rw [integral_finsetSum Finset.univ (fun j _ => (tradeClockIntegrable N z a i j).mul_const (virtual N z a j e))]
    simp only [integral_mul_const,← tradeResolventIntegral,tradeResolventRecovery]
