-- Prove2me | solution 1 for RGMISFast.query_measurable_rank_regular
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:17:05.146715+00:00
-- url     : https://prove2.me/submissions/d24130b4-4220-4b23-accd-722122a5b904

import Definitions.Def_RGMISFast_run
import Definitions.Def_RGMISFast_rankLaw
open ProbabilityTheory
open RGMISFast MeasureTheory
set_option autoImplicit false

private theorem scan_congr {V : Type} [LinearOrder V] (r s : V → ℝ)
    (h : ∀ a b, r a < r b ↔ s a < s b) (A : Finset V) :
    scanOrder r A = scanOrder s A := by
  classical
  have heq (a b : V) : r a = r b ↔ s a = s b := by
    simp only [le_antisymm_iff, ← not_lt, h]
  have hkey (a b : V) : toLex (r a, a) ≤ toLex (r b, b) ↔
      toLex (s a, a) ≤ toLex (s b, b) := by
    simp only [Prod.Lex.toLex_le_toLex, Prod.lex_iff, h, heq]
  rcases A with ⟨m, hm⟩
  induction m using Quot.ind with
  | mk l =>
    have hr := List.map_insertionSort (fun a b : V => toLex (r a,a) ≤ toLex (r b,b))
      (fun a b : ℝ ×ₗ V => a ≤ b) (fun a => toLex (r a,a)) l (by intros; rfl)
    have hs := List.map_insertionSort (fun a b : V => toLex (s a,a) ≤ toLex (s b,b))
      (fun a b : ℝ ×ₗ V => a ≤ b) (fun a => toLex (s a,a)) l (by intros; rfl)
    change ((l.map (fun a => toLex (r a,a))).insertionSort (· ≤ ·)).map (fun p => (ofLex p).2) =
      ((l.map (fun a => toLex (s a,a))).insertionSort (· ≤ ·)).map (fun p => (ofLex p).2)
    rw [← hr, ← hs]
    simp only [List.map_map, Function.comp_def, ofLex_toLex, List.map_id_fun]
    have hh : (fun a b : V => toLex (r a,a) ≤ toLex (r b,b)) =
        (fun a b : V => toLex (s a,a) ≤ toLex (s b,b)) :=
      funext fun a => funext fun b => propext (hkey a b)
    simp only [hh]

private theorem rank_index_congr {V : Type} [Fintype V] (r s : V → ℝ)
    (h : ∀ a b, r a < r b ↔ s a < s b) (v : V) : rk r v = rk s v := by
  unfold rk
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]

private theorem lower_congr {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (h : ∀ a b, r a < r b ↔ s a < s b) (v : V) : lowerNbrs G r v = lowerNbrs G s v := by
  unfold lowerNbrs
  have hf : (G.neighborFinset v).filter (fun w => r w < r v) =
      (G.neighborFinset v).filter (fun w => s w < s v) := by ext w; simp [h]
  rw [hf]
  exact scan_congr r s h _

private theorem fold_attach_congr {A B : Type} (l k : List A) (hl : l = k)
    (f : B → {x // x ∈ l} → B) (g : B → {x // x ∈ k} → B)
    (h : ∀ b x hx hy, f b ⟨x,hx⟩ = g b ⟨x,hy⟩) (b : B) :
    l.attach.foldl f b = k.attach.foldl g b := by
  subst k
  have he : f = g := funext fun b => funext fun x => h b x.val x.property x.property
  rw [he]

private theorem call_congr {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (h : ∀ a b, r a < r b ↔ s a < s b) (n : ℕ) :
    ∀ (caller : Option V) (v : V) (hr : rk r v < n) (hs : rk s v < n) (st : RunState V),
      callF G r n caller v hr st = callF G s n caller v hs st := by
  induction n with
  | zero => intro caller v hr; omega
  | succ n ih =>
    intro caller v hr hs st
    simp only [callF]
    split
    · rfl
    · have hf : _ := fold_attach_congr (lowerNbrs G r v) (lowerNbrs G s v)
        (lower_congr G r s h v)
        (fun (acc : Bool × RunState V) w => if acc.1 then acc else
          callF G r n (some v) w.val (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (fun (acc : Bool × RunState V) w => if acc.1 then acc else
          callF G s n (some v) w.val (by have := rk_lt s ((mem_lowerNbrs G s).1 w.property).2; omega) acc.2)
        (by intro acc w hw hw'; split; rfl; apply ih)
        (false, { st with count := st.count + 1, trace := st.trace ++ [⟨caller, v, true⟩] })
      rw [hf]

private theorem query_congr {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r s : V → ℝ)
    (h : ∀ a b, r a < r b ↔ s a < s b) : Q G u r = Q G u s := by
  have hi := rank_index_congr r s h u
  unfold Q run
  have he := call_congr G r s h (rk r u + 1) none u (Nat.lt_succ_self _)
    (by omega) initState
  simpa only [hi] using congrArg (fun z : Bool × RunState V => z.2.count) he

theorem query_measurable {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Measurable (fun r : V → ℝ => Q G u r) := by
  classical
  let code : (V → ℝ) → (V → V → Prop) := fun r a b => r a < r b
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurableSet_setOf.mp (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
  have hf : (fun r : V → ℝ => Q G u r).FactorsThrough code := by
    intro r s he
    apply query_congr G u r s
    intro a b
    exact iff_of_eq (congrFun (congrFun he a) b)
  obtain ⟨f, he⟩ := (Function.factorsThrough_iff _).mp hf
  rw [he]
  exact (measurable_of_countable f).comp hm

private theorem rank_regular (V : Type) [Fintype V] :
    ∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r ∧ ∀ v, 0 ≤ r v := by
  classical
  let μ : Measure ℝ := expMeasure 1
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure (by norm_num)
  letI : NullSingletonClass μ := by dsimp [μ, expMeasure, gammaMeasure]; infer_instance
  have hmap (v : V) : (RGMISFast.rankLaw V).map (fun r => r v) = μ :=
    (measurePreserving_eval (fun _ : V => μ) v).map_eq
  have hnn : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change μ (Set.Iio 0) = 0
    rw [show μ = volume.withDensity (gammaPDF 1 1) from rfl,
      withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hall : ∀ᵐ r ∂(RGMISFast.rankLaw V), ∀ v, 0 ≤ r v := by
    apply Filter.eventually_all.mpr
    intro v
    apply ae_of_ae_map (measurable_pi_apply v).aemeasurable
    rw [hmap]
    exact hnn
  have hpair (v w : V) (hvw : v ≠ w) :
      ∀ᵐ r ∂(RGMISFast.rankLaw V), r v ≠ r w := by
    have hind := (iIndepFun_pi (μ := fun _ : V => μ)
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
    have hm := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
    change (RGMISFast.rankLaw V).map (fun r => (r v, r w)) =
      ((RGMISFast.rankLaw V).map (fun r => r v)).prod ((RGMISFast.rankLaw V).map (fun r => r w)) at hm
    rw [hmap, hmap] at hm
    have hp : ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
      rw [ae_iff]
      simp only [not_not]
      apply Measure.measure_prod_null_of_ae_null
      · exact measurableSet_eq_fun measurable_fst measurable_snd
      · filter_upwards [] with x
        change μ {y : ℝ | x = y} = 0
        simp
    apply ae_of_ae_map (μ := RGMISFast.rankLaw V) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
      ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
    rw [hm]
    exact hp
  have hi : ∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r := by
    apply Filter.eventually_all.mpr
    intro v
    apply Filter.eventually_all.mpr
    intro w
    by_cases he : v = w
    · exact Filter.Eventually.of_forall (fun _ _ => he)
    · filter_upwards [hpair v w he] with r hr heq
      exact (hr heq).elim
  exact hi.and hall


theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Measurable (fun r : V → ℝ => RGMISFast.Q G u r) ∧
    (∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r ∧ ∀ v, 0 ≤ r v) :=
  ⟨query_measurable G u, rank_regular V⟩
