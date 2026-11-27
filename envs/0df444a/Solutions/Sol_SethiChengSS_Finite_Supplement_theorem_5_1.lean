-- Prove2me | solution 1 for SethiChengSS.Finite.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:44:56.329907+00:00
-- url     : https://prove2.me/submissions/bd837539-a3fd-4945-869a-aafaae8665b4

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Calendar

open SethiChengSS
open SethiChengSS.Finite
open SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.1, pp. 935–936: arbitrary no-ordering dates, with both DP attainment
and optimality over the constrained history-dependent policy class. -/
theorem solution {L : ℕ} (D : Data L) (N : ℕ) (allowed : ℕ → Prop)
    (hD : Standing D) (h41 : Cond41 D N) (h42 : Cond42 D N) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n < N, ∀ i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      (∀ n < N, InB0 (calendarRule allowed s S n)) ∧
      (∀ n < N, ∀ i x,
        (calendarObjective D n (calendarV D allowed N (n + 1)) i x ''
          calendarActions allowed n).Nonempty ∧
        BddBelow (calendarObjective D n (calendarV D allowed N (n + 1)) i x ''
          calendarActions allowed n) ∧
        calendarRule allowed s S n i x ∈ calendarActions allowed n ∧
        calendarV D allowed N n i x = D.f n i x - D.c n i * x + calendarH D allowed N n i x ∧
        calendarV D allowed N n i x = D.f n i x +
          calendarObjective D n (calendarV D allowed N (n + 1)) i x
            (calendarRule allowed s S n i x) ∧
        ∀ u ∈ calendarActions allowed n,
          calendarObjective D n (calendarV D allowed N (n + 1)) i x
            (calendarRule allowed s S n i x) ≤
          calendarObjective D n (calendarV D allowed N (n + 1)) i x u) ∧
      (∀ n < N, ∀ i j y,
        Integrable (fun z => calendarV D allowed N (n + 1) j (y - z) * D.φ n i z)
          (volume.restrict (Set.Ioi 0))) ∧
      (∀ n ≤ N, ∀ i x,
        CalendarAdmissible allowed N n (feedback (calendarRule allowed s S) n x) ∧
        0 ≤ calendarV D allowed N n i x ∧
        J D N n i x (feedback (calendarRule allowed s S) n x) =
          ENNReal.ofReal (calendarV D allowed N n i x) ∧
        calendarValue D allowed N n i x = ENNReal.ofReal (calendarV D allowed N n i x) ∧
        ∀ U : Policy L, CalendarAdmissible allowed N n U →
          J D N n i x (feedback (calendarRule allowed s S) n x) ≤ J D N n i x U) := by
            classical
            have key : ∀ (V : ℕ → Fin L → ℝ → ℝ), (∀ i x, V N i x = D.f N i x) → (∀ n i x, 0 ≤ V n i x) →
                (∀ n < N, ∀ i j y, Integrable (fun z => V (n + 1) j (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0))) →
                ∀ (r : ℕ → Fin L → ℝ → ℝ),
                (∀ n < N, ∀ i x, V n i x = D.f n i x + calendarObjective D n (V (n + 1)) i x (r n i x)) →
                (∀ n < N, ∀ i x, ∀ u ∈ calendarActions allowed n,
                  calendarObjective D n (V (n+1)) i x (r n i x) ≤ calendarObjective D n (V (n+1)) i x u) →
                (∀ n x, CalendarAdmissible allowed N n (feedback r n x)) →
                ∀ n ≤ N, ∀ i x, J D N n i x (feedback r n x) = ENNReal.ofReal (V n i x) ∧
                  ∀ U : Policy L, CalendarAdmissible allowed N n U → ENNReal.ofReal (V n i x) ≤ J D N n i x U := by
              intro V hVN hVnn hInt r hV2 hopt hadm
              let E : ∀ m : ℕ, ℕ → Fin L → ((Fin (m+1) → Fin L) → (Fin m → ℝ) → ℝ≥0∞) → ℝ≥0∞ :=
                fun m n i h => ∑ σ : Fin (m + 1) → Fin L, if σ 0 = i then
                  ∫⁻ ξ : Fin m → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) * h σ ξ else 0
              have hcons_meas : ∀ m, Measurable (fun p : ℝ × (Fin m → ℝ) => (Fin.cons p.1 p.2 : Fin (m+1) → ℝ)) := by
                intro m
                refine measurable_pi_lambda _ fun k => ?_
                refine Fin.cases ?_ (fun k => ?_) k
                · simpa using measurable_fst
                · simp only [Fin.cons_succ]; exact (measurable_pi_apply k).comp measurable_snd
              have hw_meas : ∀ n m (σ : Fin (m+1) → Fin L), Measurable (pathWeight D n σ) := by
                intro n m σ
                unfold pathWeight
                exact Finset.measurable_prod _ fun t _ => measurable_const.mul ((hD.φ_meas _ _).comp (measurable_pi_apply t))
              have hw_nn : ∀ n m (σ : Fin (m+1) → Fin L) ξ, 0 ≤ pathWeight D n σ ξ := fun n m σ ξ =>
                Finset.prod_nonneg fun t _ => mul_nonneg (hD.P_nonneg _ _) (hD.φ_nonneg _ _ _)
              have hw_cons : ∀ n m i (σ : Fin (m+1) → Fin L) z (ξ : Fin m → ℝ),
                  pathWeight D n (Fin.cons i σ) (Fin.cons z ξ) = D.P i (σ 0) * D.φ n i z * pathWeight D (n+1) σ ξ := by
                intro n m i σ z ξ
                unfold pathWeight
                rw [Fin.prod_univ_succ]
                congr 1
                refine Finset.prod_congr rfl fun t _ => ?_
                simp only [Fin.cons_succ, Fin.val_succ, ← Fin.succ_castSucc]
                rw [show n + (↑t + 1) = n + 1 + ↑t by ring]
              have hfub : ∀ m (g : (Fin (m+1) → ℝ) → ℝ≥0∞), Measurable g →
                  ∫⁻ ξ, g ξ = ∫⁻ z, ∫⁻ ξ' : Fin m → ℝ, g (Fin.cons z ξ') := by
                intro m g hg
                have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
                rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
                rw [Measure.volume_eq_prod, lintegral_prod (fun a => g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm a))
                  ((hg.comp (MeasurableEquiv.measurable _)).aemeasurable)]
                simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
              have hφlin : ∀ k i, ∫⁻ z, ENNReal.ofReal (D.φ k i z) = 1 := by
                intro k i
                have hφI : Integrable (D.φ k i) :=
                  Integrable.of_integral_ne_zero (by rw [hD.φ_int]; norm_num)
                rw [← ofReal_integral_eq_lintegral_ofReal hφI (Eventually.of_forall (hD.φ_nonneg k i)), hD.φ_int]
                simp
              have hsumP : ∀ i, ∑ j, ENNReal.ofReal (D.P i j) = 1 := by
                intro i
                rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.P_nonneg i j), hD.P_sum]; simp
              have hEstep : ∀ m n i (h : (Fin (m+2) → Fin L) → (Fin (m+1) → ℝ) → ℝ≥0∞), (∀ σ, Measurable (h σ)) →
                  E (m+1) n i h = ∑ j, ENNReal.ofReal (D.P i j) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                    E m (n+1) j (fun σ' ξ' => h (Fin.cons i σ') (Fin.cons z ξ')) := by
                intro m n i h hh
                have hL : E (m+1) n i h = ∑ σ' : Fin (m+1) → Fin L, ∫⁻ ξ : Fin (m+1) → ℝ,
                    ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) * h (Fin.cons i σ') ξ := by
                  simp only [E]
                  rw [← (Fin.consEquiv (fun _ => Fin L)).sum_comp, Fintype.sum_prod_type]
                  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero]
                  rw [Finset.sum_eq_single i]
                  · simp
                  · intro b _ hb; simp [hb]
                  · simp
                have hmeasI : ∀ (σ' : Fin (m+1) → Fin L), Measurable (fun p : ℝ × (Fin m → ℝ) =>
                    ENNReal.ofReal (pathWeight D (n+1) σ' p.2) * h (Fin.cons i σ') (Fin.cons p.1 p.2)) := by
                  intro σ'
                  exact (ENNReal.measurable_ofReal.comp ((hw_meas _ _ σ').comp measurable_snd)).mul
                    ((hh _).comp (hcons_meas m))
                rw [hL]
                have hR : ∀ j, ENNReal.ofReal (D.P i j) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                    E m (n+1) j (fun σ' ξ' => h (Fin.cons i σ') (Fin.cons z ξ')) =
                    ∑ σ' : Fin (m+1) → Fin L, if σ' 0 = j then ENNReal.ofReal (D.P i (σ' 0)) *
                      ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ') *
                        h (Fin.cons i σ') (Fin.cons z ξ') else 0 := by
                  intro j
                  simp only [E, Finset.mul_sum]
                  rw [lintegral_finset_sum']
                  · rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun σ' _ => ?_
                    split_ifs with hj
                    · rw [hj]
                    · simp
                  · intro σ' _
                    refine ((ENNReal.measurable_ofReal.comp (hD.φ_meas n i)).mul ?_).aemeasurable
                    split_ifs
                    · exact (hmeasI σ').lintegral_prod_right'
                    · exact measurable_const
                simp_rw [hR]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun σ' _ => ?_
                rw [Finset.sum_ite_eq]
                simp only [Finset.mem_univ, if_true]
                rw [hfub m (fun ξ => ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) * h (Fin.cons i σ') ξ)
                  ((ENNReal.measurable_ofReal.comp (hw_meas _ _ _)).mul (hh _))]
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun z => ?_
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun ξ' => ?_
                rw [hw_cons, ENNReal.ofReal_mul (mul_nonneg (hD.P_nonneg _ _) (hD.φ_nonneg _ _ _)),
                  ENNReal.ofReal_mul (hD.P_nonneg _ _)]
                ring
              have hE1 : ∀ m n i, E m n i (fun _ _ => 1) = 1 := by
                intro m
                induction m with
                | zero =>
                  intro n i
                  simp only [E]
                  rw [Fintype.sum_eq_single (fun _ => i)]
                  · simp [pathWeight]
                    rw [MeasureTheory.volume_pi, Measure.pi_empty_univ]
                  · intro σ hσ
                    rw [if_neg]
                    intro h0; apply hσ; funext k; rw [show k = 0 from Fin.ext (by omega), h0]
                | succ m ih =>
                  intro n i
                  rw [hEstep m n i _ (fun _ => measurable_const)]
                  simp only [ih, mul_one, hφlin, hsumP]

              have hEcongr : ∀ m n i (h h' : (Fin (m+1) → Fin L) → (Fin m → ℝ) → ℝ≥0∞),
                  (∀ σ ξ, σ 0 = i → h σ ξ = h' σ ξ) → E m n i h = E m n i h' := by
                intro m n i h h' hh
                refine Finset.sum_congr rfl fun σ _ => ?_
                split_ifs with h0
                · exact lintegral_congr fun ξ => by rw [hh σ ξ h0]
                · rfl
              have hEadd : ∀ m n i (c : ℝ≥0∞) (h : (Fin (m+1) → Fin L) → (Fin m → ℝ) → ℝ≥0∞),
                  c ≠ ⊤ → E m n i (fun σ ξ => c + h σ ξ) = c + E m n i h := by
                intro m n i c h hc
                have h1 := hE1 m n i
                have : E m n i (fun σ ξ => c + h σ ξ) = c * E m n i (fun _ _ => 1) + E m n i h := by
                  simp only [E, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun σ _ => ?_
                  split_ifs
                  · rw [← lintegral_const_mul' _ _ hc, ← lintegral_add_left]
                    · exact lintegral_congr fun ξ => by ring
                    · exact Measurable.const_mul (Measurable.mul_const (ENNReal.measurable_ofReal.comp (hw_meas _ _ _)) _) _
                  · simp
                rw [this, h1, mul_one]
              have hic : ∀ {α : Type} (k : ℕ) (a : α) (f : Fin (k+1) → α),
                  Fin.init (Fin.cons a f : Fin (k+2) → α) = Fin.cons a (Fin.init f) := by
                intro α k a f; funext j
                refine Fin.cases ?_ (fun j => ?_) j
                · rfl
                · rfl
              let sh : Policy L → Fin L → ℝ → Policy L := fun U i z t σ ξ => U (t+1) (Fin.cons i σ) (Fin.cons z ξ)
              have hsurp : ∀ (U : Policy L) x i z t (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ),
                  surplus U x (t+1) (Fin.cons i σ) (Fin.cons z ξ) =
                    surplus (sh U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t σ ξ := by
                intro U x i z t
                induction t with
                | zero =>
                  intro σ ξ
                  simp only [surplus]
                  have e1 : (Fin.init (Fin.cons i σ : Fin 2 → Fin L) : Fin 1 → Fin L) = fun _ => i := by
                    funext k; rw [show k = 0 from Fin.ext (by omega)]; rfl
                  have e2 : (Fin.init (Fin.cons z ξ : Fin 1 → ℝ) : Fin 0 → ℝ) = Fin.elim0 := by
                    funext k; exact k.elim0
                  rw [e1, e2]; rfl
                | succ t ih =>
                  intro σ ξ
                  rw [surplus, hic, hic, ih, surplus]
                  rfl
              have his : ∀ {α : Type} (m t : ℕ) (a : α) (f : Fin (m+1) → α) (h1 : t + 1 ≤ m + 1) (h2 : t ≤ m),
                  (fun j : Fin (t+2) => (Fin.cons a f : Fin (m+2) → α) ⟨j.1, by have := j.2; omega⟩) =
                    Fin.cons a (fun j : Fin (t+1) => f ⟨j.1, by have := j.2; omega⟩) := by
                intro α m t a f h1 h2; funext j
                refine Fin.cases ?_ (fun j => ?_) j
                · rfl
                · rfl
              have hid : ∀ {α : Type} (m t : ℕ) (a : α) (f : Fin m → α) (h1 : t + 1 ≤ m + 1) (h2 : t ≤ m),
                  (fun j : Fin (t+1) => (Fin.cons a f : Fin (m+1) → α) ⟨j.1, by have := j.2; omega⟩) =
                    Fin.cons a (fun j : Fin t => f ⟨j.1, by have := j.2; omega⟩) := by
                intro α m t a f h1 h2; funext j
                refine Fin.cases ?_ (fun j => ?_) j
                · rfl
                · rfl
              have hpc : ∀ (U : Policy L) x n m i (σ : Fin (m+1) → Fin L) z (ξ : Fin m → ℝ),
                  pathCost D N n U x (Fin.cons i σ) (Fin.cons z ξ) =
                    orderCost D n i (U 0 (fun _ => i) Fin.elim0) + D.f n i x +
                    pathCost D N (n+1) (sh U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) σ ξ := by
                intro U x n m i σ z ξ
                unfold pathCost
                rw [Fin.sum_univ_succ, hsurp]
                simp only [Fin.val_succ, Fin.val_zero, Fin.cons_zero, Fin.castSucc_zero, Fin.succ_castSucc, Fin.cons_succ,
                  Fin.succ_last]
                have h0s : initStates (Fin.cons i σ : Fin (m+2) → Fin L) 0 (by omega) = fun _ => i := by
                  funext k; rw [show k = 0 from Fin.ext (by omega)]; rfl
                have h0d : initDemands (Fin.cons z ξ : Fin (m+1) → ℝ) 0 (by omega) = Fin.elim0 := by
                  funext k; exact k.elim0
                have hlast : (Fin.cons i σ : Fin (m+2) → Fin L) (Fin.last (m+1)) = σ (Fin.last m) := by
                  rw [← Fin.succ_last, Fin.cons_succ]
                rw [h0s, h0d, hlast]
                simp only [add_zero, surplus.eq_1, add_assoc]
                refine congrArg (_ + ·) (congrArg (_ + ·) (congrArg (· + _) ?_))
                refine Finset.sum_congr rfl fun t _ => ?_
                have hs1 : initStates (Fin.cons i σ : Fin (m+2) → Fin L) (↑t + 1) (by omega) =
                    Fin.cons i (initStates σ t (by omega)) := his m t i σ (by omega) (by omega)
                have hd1 : initDemands (Fin.cons z ξ : Fin (m+1) → ℝ) (↑t + 1) (by omega) =
                    Fin.cons z (initDemands ξ t (by omega)) := hid m t z ξ (by omega) (by omega)
                have hc : (Fin.cons i σ : Fin (m+2) → Fin L) t.succ.castSucc = σ t.castSucc := by
                  rw [← Fin.succ_castSucc, Fin.cons_succ]
                rw [hs1, hd1, hsurp, hc, show n + (↑t + 1) = n + 1 + ↑t by ring]
                rw [show n + (1 + (t:ℕ)) = n + 1 + t by ring]
              have hfm : ∀ k j, Measurable (D.f k j) := by
                intro k j
                have hf := (hD.f_convex k j).continuousOn_interior
                rw [interior_univ] at hf
                exact (continuousOn_univ.mp hf).measurable
              have hoc_nn : ∀ k i u, 0 ≤ u → 0 ≤ orderCost D k i u := by
                intro k i u hu
                unfold orderCost
                exact add_nonneg (mul_nonneg (hD.K_nonneg _ _) (by unfold delta; split_ifs <;> norm_num))
                  (mul_nonneg (hD.c_nonneg _ _) hu)
              have hoc_meas : ∀ k i, Measurable (orderCost D k i) := by
                intro k i
                unfold orderCost
                refine (measurable_const.mul ?_).add (measurable_const.mul measurable_id)
                unfold delta
                exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
              have hpc_nn : ∀ (U : Policy L) n x m (σ : Fin (m+1) → Fin L) (ξ : Fin m → ℝ),
                  (∀ t < m, ∀ σ ξ, 0 ≤ U t σ ξ) → 0 ≤ pathCost D N n U x σ ξ := by
                intro U n x m σ ξ hU
                unfold pathCost
                exact add_nonneg (Finset.sum_nonneg fun t _ => add_nonneg (hoc_nn _ _ _ (hU t t.2 _ _))
                  (hD.f_nonneg _ _ _)) (hD.f_nonneg _ _ _)
              have hsurp_meas : ∀ (U : Policy L) x t, (∀ t' < t, ∀ σ, Measurable (U t' σ)) →
                  ∀ σ : Fin (t+1) → Fin L, Measurable (surplus U x t σ) := by
                intro U x t
                induction t with
                | zero => intro _ σ; exact measurable_const
                | succ t ih =>
                  intro hU σ
                  have hinit : Measurable (fun ξ : Fin (t + 1) → ℝ => (Fin.init ξ : Fin t → ℝ)) :=
                    measurable_pi_lambda _ fun j => measurable_pi_apply _
                  have h1 := (ih (fun t' ht' => hU t' (by omega)) (Fin.init σ)).comp hinit
                  exact (h1.add ((hU t (by omega) _).comp hinit)).sub (measurable_pi_apply _)
              have hpc_meas : ∀ (U : Policy L) n x m (σ : Fin (m+1) → Fin L), (∀ t < m, ∀ σ, Measurable (U t σ)) →
                  Measurable (fun ξ : Fin m → ℝ => pathCost D N n U x σ ξ) := by
                intro U n x m σ hU
                unfold pathCost
                have hid' : ∀ t (ht : t ≤ m), Measurable (fun ξ : Fin m → ℝ => initDemands ξ t ht) := fun t ht =>
                  measurable_pi_lambda _ fun j => measurable_pi_apply _
                refine Measurable.add (Finset.measurable_sum _ fun t _ => ?_) ?_
                · refine Measurable.add ?_ ?_
                  · exact (hoc_meas _ _).comp ((hU t t.2 _).comp (hid' _ _))
                  · exact (hfm _ _).comp ((hsurp_meas U x t (fun t' ht' => hU t' (by omega)) _).comp (hid' _ _))
                · exact (hfm _ _).comp (hsurp_meas U x m hU σ)
              have hE0 : ∀ m n i, E m n i (fun _ _ => 0) = 0 := by intro m n i; simp [E]
              have hEconst : ∀ m n i (c : ℝ≥0∞), c ≠ ⊤ → E m n i (fun _ _ => c) = c := by
                intro m n i c hc
                have := hEadd m n i c (fun _ _ => 0) hc
                simp only [add_zero] at this
                rw [this, hE0, add_zero]
              have hinner : ∀ n < N, ∀ i j y, ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (V (n+1) j (y - z)) =
                  ENNReal.ofReal (∫ z in Set.Ioi 0, V (n+1) j (y - z) * D.φ n i z) := by
                intro n hn i j y
                rw [ofReal_integral_eq_lintegral_ofReal (hInt n hn i j y)
                  (Eventually.of_forall fun z => mul_nonneg (hVnn _ _ _) (hD.φ_nonneg _ _ _))]
                rw [← lintegral_add_compl _ (measurableSet_Ioi (a := (0:ℝ)))]
                have h0 : ∫⁻ z in (Set.Ioi (0:ℝ))ᶜ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (V (n+1) j (y - z)) = 0 := by
                  rw [Set.compl_Ioi, setLIntegral_congr Iio_ae_eq_Iic.symm]
                  have : ∫⁻ z in Set.Iio (0:ℝ), ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (V (n+1) j (y - z)) =
                      ∫⁻ z in Set.Iio (0:ℝ), 0 :=
                    setLIntegral_congr_fun measurableSet_Iio (fun z hz => by simp [hD.φ_neg _ _ _ hz])
                  rw [this, lintegral_zero]
                rw [h0, add_zero]
                refine setLIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
                rw [ENNReal.ofReal_mul (hVnn _ _ _), mul_comm]
              have hkey : ∀ n < N, ∀ i y (c : ℝ), 0 ≤ c →
                  ∑ j, ENNReal.ofReal (D.P i j) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                    (ENNReal.ofReal c + ENNReal.ofReal (V (n+1) j (y - z))) =
                  ENNReal.ofReal (c + F D n (V (n+1)) i y) := by
                intro n hn i y c hc
                have h1 : ∀ j, ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                    (ENNReal.ofReal c + ENNReal.ofReal (V (n+1) j (y - z))) =
                    ENNReal.ofReal c + ENNReal.ofReal (∫ z in Set.Ioi 0, V (n+1) j (y - z) * D.φ n i z) := by
                  intro j
                  simp_rw [mul_add]
                  have hm : Measurable (fun z => ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal c) :=
                    (ENNReal.measurable_ofReal.comp (hD.φ_meas n i)).mul_const _
                  rw [lintegral_add_left hm,
                    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hφlin, one_mul, hinner n hn i j y]
                simp_rw [h1, mul_add]
                rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumP, one_mul]
                have hI : ∀ j, 0 ≤ ∫ z in Set.Ioi 0, V (n+1) j (y - z) * D.φ n i z := fun j =>
                  integral_nonneg fun z => mul_nonneg (hVnn _ _ _) (hD.φ_nonneg _ _ _)
                unfold F
                rw [ENNReal.ofReal_add hc (Finset.sum_nonneg fun j _ => mul_nonneg (hD.P_nonneg _ _) (hI j))]
                congr 1
                rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hD.P_nonneg _ _) (hI j))]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [ENNReal.ofReal_mul (hD.P_nonneg _ _)]
              have hJstep : ∀ m n (U : Policy L) i x, (∀ t < m+1, (∀ σ ξ, 0 ≤ U t σ ξ) ∧ ∀ σ, Measurable (U t σ)) →
                  E (m+1) n i (fun σ ξ => ENNReal.ofReal (pathCost D N n U x σ ξ)) =
                  ∑ j, ENNReal.ofReal (D.P i j) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                    (ENNReal.ofReal (orderCost D n i (U 0 (fun _ => i) Fin.elim0) + D.f n i x) +
                      E m (n+1) j (fun σ ξ => ENNReal.ofReal
                        (pathCost D N (n+1) (sh U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) σ ξ))) := by
                intro m n U i x hU
                rw [hEstep m n i (fun σ ξ => ENNReal.ofReal (pathCost D N n U x σ ξ)) (fun σ => ENNReal.measurable_ofReal.comp
                  (hpc_meas U n x (m+1) σ (fun t ht => (hU t ht).2)))]
                refine Finset.sum_congr rfl fun j _ => ?_
                refine congrArg (_ * ·) (lintegral_congr fun z => congrArg (_ * ·) ?_)
                rw [← hEadd _ _ _ _ _ ENNReal.ofReal_ne_top]
                refine congrArg _ (funext fun σ' => funext fun ξ' => ?_)
                rw [hpc, ENNReal.ofReal_add (add_nonneg (hoc_nn _ _ _ ((hU 0 (by omega)).1 _ _)) (hD.f_nonneg _ _ _))
                  (hpc_nn _ _ _ _ _ _ (fun t ht σ ξ => (hU (t+1) (by omega)).1 _ _))]
              have hfbs : ∀ n x i z t (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ),
                  fbSurplus r n x (t+1) (Fin.cons i σ) (Fin.cons z ξ) = fbSurplus r (n+1) (x + r n i x - z) t σ ξ := by
                intro n x i z t
                induction t with
                | zero => intro σ ξ; rfl
                | succ t ih =>
                  intro σ ξ
                  rw [fbSurplus, hic, hic, ih, fbSurplus]
                  have hl : (Fin.cons i (Fin.init σ) : Fin (t+2) → Fin L) (Fin.last (t+1)) = Fin.init σ (Fin.last t) := by
                    rw [← Fin.succ_last, Fin.cons_succ]
                  have hl2 : (Fin.cons z ξ : Fin (t+2) → ℝ) (Fin.last (t+1)) = ξ (Fin.last t) := by
                    rw [← Fin.succ_last, Fin.cons_succ]
                  rw [hl, hl2, show n + (t+1) = n + 1 + t by ring]
              have hsh_fb : ∀ n x i z, sh (feedback r n x) i z = feedback r (n+1) (x + r n i x - z) := by
                intro n x i z
                funext t σ ξ
                show r (n + (t+1)) ((Fin.cons i σ : Fin (t+2) → Fin L) (Fin.last (t+1)))
                  (fbSurplus r n x (t+1) (Fin.cons i σ) (Fin.cons z ξ)) = r (n+1+t) (σ (Fin.last t)) _
                rw [hfbs, show n + (t+1) = n + 1 + t by ring, ← Fin.succ_last, Fin.cons_succ]
              have hmain : ∀ m n, n + m = N → ∀ i x,
                  E m n i (fun σ ξ => ENNReal.ofReal (pathCost D N n (feedback r n x) x σ ξ)) = ENNReal.ofReal (V n i x) ∧
                  ∀ U : Policy L, (∀ t < m, (∀ σ ξ, 0 ≤ U t σ ξ) ∧ ∀ σ, Measurable (U t σ)) →
                    (∀ t < m, ∀ σ ξ, ¬ allowed (n + t) → U t σ ξ = 0) →
                    ENNReal.ofReal (V n i x) ≤ E m n i (fun σ ξ => ENNReal.ofReal (pathCost D N n U x σ ξ)) := by
                intro m
                induction m with
                | zero =>
                  intro n hn i x
                  have hn' : n = N := by omega
                  have hbase : ∀ U : Policy L, E 0 n i (fun σ ξ => ENNReal.ofReal (pathCost D N n U x σ ξ)) =
                      ENNReal.ofReal (V n i x) := by
                    intro U
                    rw [hEcongr 0 n i _ (fun _ _ => ENNReal.ofReal (D.f N i x)), hEconst _ _ _ _ ENNReal.ofReal_ne_top,
                      hn', hVN]
                    intro σ ξ h0
                    simp [pathCost, surplus, ← h0]
                  exact ⟨hbase _, fun U _ _ => (hbase U).ge⟩
                | succ m ih =>
                  intro n hn i x
                  have hnN : n < N := by omega
                  have ih' := ih (n+1) (by omega)
                  constructor
                  · rw [hJstep m n _ i x (fun t _ => ((hadm n x).1 t (by omega)))]
                    have hu0 : feedback r n x 0 (fun _ => i) Fin.elim0 = r n i x := rfl
                    simp_rw [hu0]
                    have : ∀ j z, E m (n+1) j (fun σ ξ => ENNReal.ofReal
                        (pathCost D N (n+1) (sh (feedback r n x) i z) (x + r n i x - z) σ ξ)) =
                        ENNReal.ofReal (V (n+1) j (x + r n i x - z)) := by
                      intro j z; rw [hsh_fb]; exact (ih' j _).1
                    simp_rw [this]
                    have hrnn : 0 ≤ r n i x := ((hadm n x).1 0 (by omega)).1 (fun _ => i) Fin.elim0
                    rw [hkey n hnN i (x + r n i x) (orderCost D n i (r n i x) + D.f n i x) (add_nonneg (hoc_nn _ _ _ hrnn)
                      (hD.f_nonneg _ _ _)), hV2 n hnN i x]
                    congr 1; unfold calendarObjective; ring
                  · intro U hU hcal
                    rw [hJstep m n U i x hU]
                    set u0 := U 0 (fun _ => i) Fin.elim0 with hu0def
                    have hu0 : u0 ∈ calendarActions allowed n :=
                      ⟨(hU 0 (by omega)).1 _ _, fun ha => hcal 0 (by omega) _ _ ha⟩
                    have hshU : ∀ z, (∀ t < m, (∀ σ ξ, 0 ≤ sh U i z t σ ξ) ∧ ∀ σ, Measurable (sh U i z t σ)) ∧
                        (∀ t < m, ∀ σ ξ, ¬ allowed (n + 1 + t) → sh U i z t σ ξ = 0) := by
                      intro z
                      refine ⟨fun t ht => ⟨fun σ ξ => (hU (t+1) (by omega)).1 _ _, fun σ => ?_⟩, fun t ht σ ξ ha => ?_⟩
                      · exact ((hU (t+1) (by omega)).2 _).comp ((hcons_meas t).comp (measurable_const.prodMk measurable_id))
                      · exact hcal (t+1) (by omega) _ _ (by rwa [show n + (t+1) = n + 1 + t by ring])
                    calc ENNReal.ofReal (V n i x)
                        ≤ ENNReal.ofReal (orderCost D n i u0 + D.f n i x + F D n (V (n+1)) i (x + u0)) := by
                          apply ENNReal.ofReal_le_ofReal
                          rw [hV2 n hnN i x]
                          have := hopt n hnN i x u0 hu0
                          unfold calendarObjective at this ⊢; linarith
                      _ = ∑ j, ENNReal.ofReal (D.P i j) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                            (ENNReal.ofReal (orderCost D n i u0 + D.f n i x) + ENNReal.ofReal (V (n+1) j (x + u0 - z))) :=
                          (hkey n hnN i (x + u0) _ (add_nonneg (hoc_nn _ _ _ hu0.1) (hD.f_nonneg _ _ _))).symm
                      _ ≤ _ := by
                          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (lintegral_mono fun z => ?_) zero_le
                          exact mul_le_mul_of_nonneg_left (add_le_add_right ((ih' j _).2 _ (hshU z).1 (hshU z).2) _) zero_le
              intro n hn i x
              have h := hmain (N - n) n (by omega) i x
              exact ⟨h.1, fun U hU => h.2 U hU.1 hU.2⟩
            set V := calendarV D allowed N with hVdef
            -- unfolding of the recursion
            have hVsucc : ∀ n < N, ∀ i x, V n i x = D.f n i x +
                sInf (calendarObjective D n (V (n+1)) i x '' calendarActions allowed n) := by
              intro n hn i x
              have h1 : N - n = (N - (n+1)) + 1 := by omega
              have h2 : N - ((N - (n+1)) + 1) = n := by omega
              simp only [hVdef, calendarV, h1, calendarAux, h2]
            have hVN : ∀ i x, V N i x = D.f N i x := by
              intro i x; simp [hVdef, calendarV, calendarAux]

            have hAuxnn : ∀ m i x, 0 ≤ calendarAux D allowed N m i x := by
                intro m
                induction m with
                | zero => intro i x; exact hD.f_nonneg _ _ _
                | succ m ih =>
                  intro i x
                  simp only [calendarAux]
                  refine add_nonneg (hD.f_nonneg _ _ _) (Real.sInf_nonneg ?_)
                  rintro _ ⟨u, hu, rfl⟩
                  unfold calendarObjective orderCost F
                  refine add_nonneg (add_nonneg (mul_nonneg (hD.K_nonneg _ _) ?_)
                    (mul_nonneg (hD.c_nonneg _ _) hu.1)) ?_
                  · unfold delta; split_ifs <;> norm_num
                  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hD.P_nonneg _ _)
                      (integral_nonneg fun z => mul_nonneg (ih _ _) (hD.φ_nonneg _ _ _))
            have hVnn : ∀ n i x, 0 ≤ V n i x := by
              intro n i x; exact hAuxnn _ _ _
            have hobj_nn : ∀ n i x u, 0 ≤ u → 0 ≤ calendarObjective D n (V (n+1)) i x u := by
              intro n i x u hu
              unfold calendarObjective orderCost F
              refine add_nonneg (add_nonneg (mul_nonneg (hD.K_nonneg _ _) ?_)
                (mul_nonneg (hD.c_nonneg _ _) hu)) ?_
              · unfold delta; split_ifs <;> norm_num
              · exact Finset.sum_nonneg fun j _ => mul_nonneg (hD.P_nonneg _ _)
                  (integral_nonneg fun z => mul_nonneg (hVnn _ _ _) (hD.φ_nonneg _ _ _))
            -- the hard core: integrability and (s,S) attainment
            have hIntB : (∀ n < N, ∀ i j y,
                Integrable (fun z => V (n + 1) j (y - z) * D.φ n i z) (volume.restrict (Set.Ioi 0))) ∧
                ∀ m j, ∃ C, 0 ≤ C ∧ ∀ x, calendarAux D allowed N m j x ≤ C * (1 + |x|) := by
              have hIntGen : ∀ (b : Fin L → ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ j, Measurable (b j)) →
                  (∀ j x, 0 ≤ b j x) → (∀ j x, b j x ≤ C * (1 + |x|)) → ∀ k i j y,
                  Integrable (fun z => b j (y - z) * D.φ k i z) (volume.restrict (Set.Ioi 0)) ∧
                  ∫ z in Set.Ioi 0, b j (y - z) * D.φ k i z ≤ C * (1 + |y|) + C * D.M := by
                intro b C hC hbm hb0 hbC k i j y
                have hφI : Integrable (D.φ k i) :=
                  Integrable.of_integral_ne_zero (by rw [hD.φ_int]; norm_num)
                have hzI := hD.mean_integrable k i
                have hgI : Integrable (fun z => C * (1 + |y|) * D.φ k i z + C * (z * D.φ k i z)) :=
                  (hφI.const_mul _).add (hzI.const_mul _)
                have hbound : ∀ z ∈ Set.Ioi (0:ℝ), b j (y - z) * D.φ k i z ≤
                    C * (1 + |y|) * D.φ k i z + C * (z * D.φ k i z) := by
                  intro z hz
                  have hz0 : 0 < z := hz
                  have h1 := hbC j (y - z)
                  have h2 : |y - z| ≤ |y| + z := by
                    have := abs_sub y z; rw [abs_of_pos hz0] at this; linarith
                  have hφ := hD.φ_nonneg k i z
                  nlinarith [mul_le_mul_of_nonneg_right h1 hφ, mul_le_mul_of_nonneg_right h2 (mul_nonneg hC hφ)]
                have hmeas : AEStronglyMeasurable (fun z => b j (y - z) * D.φ k i z)
                    (volume.restrict (Set.Ioi 0)) :=
                  (((hbm j).comp (measurable_const.sub measurable_id)).mul (hD.φ_meas k i)).aestronglyMeasurable
                have hI : Integrable (fun z => b j (y - z) * D.φ k i z) (volume.restrict (Set.Ioi 0)) := by
                  refine Integrable.mono' hgI.restrict hmeas ?_
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
                  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb0 _ _) (hD.φ_nonneg _ _ _))]
                  exact hbound z hz
                refine ⟨hI, ?_⟩
                have hnn : ∀ z, 0 ≤ C * (1 + |y|) * D.φ k i z + C * (z * D.φ k i z) := by
                  intro z
                  have hφ := hD.φ_nonneg k i z
                  have : 0 ≤ z * D.φ k i z := by
                    rcases lt_or_ge z 0 with hz | hz
                    · rw [hD.φ_neg k i z hz, mul_zero]
                    · exact mul_nonneg hz hφ
                  have : 0 ≤ 1 + |y| := by positivity
                  positivity
                calc ∫ z in Set.Ioi 0, b j (y - z) * D.φ k i z
                    ≤ ∫ z in Set.Ioi 0, (C * (1 + |y|) * D.φ k i z + C * (z * D.φ k i z)) :=
                      setIntegral_mono_on hI hgI.integrableOn measurableSet_Ioi hbound
                  _ ≤ ∫ z, (C * (1 + |y|) * D.φ k i z + C * (z * D.φ k i z)) :=
                      setIntegral_le_integral hgI (Eventually.of_forall hnn)
                  _ = C * (1 + |y|) + C * ∫ z, z * D.φ k i z := by
                      rw [integral_add (hφI.const_mul _) (hzI.const_mul _), integral_const_mul,
                        integral_const_mul, hD.φ_int, mul_one]
                  _ ≤ _ := by gcongr; exact hD.mean_le k i
              have hFmeas : ∀ (b : Fin L → ℝ → ℝ), (∀ j, Measurable (b j)) → ∀ k i,
                  Measurable (F D k b i) := by
                intro b hbm k i
                unfold F
                refine Finset.measurable_sum _ fun j _ => (measurable_const.mul ?_)
                exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioi 0))
                  (f := fun y z => b j (y - z) * D.φ k i z)
                  (((hbm j).comp measurable_sub).mul ((hD.φ_meas k i).comp measurable_snd)).stronglyMeasurable).measurable
              have hstep : ∀ (b : Fin L → ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ j, Measurable (b j)) →
                  (∀ j x, 0 ≤ b j x) → (∀ j x, b j x ≤ C * (1 + |x|)) → ∀ k i,
                  Measurable (fun x => sInf (calendarObjective D k b i x '' calendarActions allowed k)) ∧
                  ∀ x, sInf (calendarObjective D k b i x '' calendarActions allowed k) ≤
                    C * (1 + |x|) + C * D.M := by
                intro b C hC hbm hb0 hbC k i
                have hFnn : ∀ y, 0 ≤ F D k b i y := fun y => Finset.sum_nonneg fun j _ =>
                  mul_nonneg (hD.P_nonneg _ _) (integral_nonneg fun z => mul_nonneg (hb0 _ _) (hD.φ_nonneg _ _ _))
                have hFle : ∀ y, F D k b i y ≤ C * (1 + |y|) + C * D.M := by
                  intro y; unfold F
                  calc ∑ j, D.P i j * ∫ z in Set.Ioi 0, b j (y - z) * D.φ k i z
                      ≤ ∑ j, D.P i j * (C * (1 + |y|) + C * D.M) :=
                        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
                          (hIntGen b C hC hbm hb0 hbC k i j y).2 (hD.P_nonneg _ _)
                    _ = _ := by rw [← Finset.sum_mul, hD.P_sum, one_mul]
                have hobjnn : ∀ x u, 0 ≤ u → 0 ≤ calendarObjective D k b i x u := by
                  intro x u hu
                  unfold calendarObjective orderCost
                  refine add_nonneg (add_nonneg (mul_nonneg (hD.K_nonneg _ _) ?_)
                    (mul_nonneg (hD.c_nonneg _ _) hu)) (hFnn _)
                  unfold delta; split_ifs <;> norm_num
                have hbdd : ∀ x, BddBelow (calendarObjective D k b i x '' calendarActions allowed k) :=
                  fun x => ⟨0, by rintro _ ⟨u, hu, rfl⟩; exact hobjnn x u hu.1⟩
                have h0 : ∀ x, calendarObjective D k b i x 0 = F D k b i x := by
                  intro x; simp [calendarObjective, orderCost, delta]
                refine ⟨?_, fun x => ?_⟩
                · by_cases ha : allowed k
                  · have hact : calendarActions allowed k = insert 0 (Set.Ioi 0) := by
                      ext u
                      simp only [calendarActions, ha, not_true_eq_false, false_implies, and_true,
                        Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_Ioi]
                      constructor
                      · intro h; rcases h.eq_or_lt with h | h
                        · exact Or.inl h.symm
                        · exact Or.inr h
                      · rintro (h | h)
                        · exact h.symm ▸ le_rfl
                        · exact h.le
                    let m : ℝ → ℝ := fun x => sInf ((fun y => D.c k i * y + F D k b i y) '' Set.Ioi x)
                    have hmbdd : ∀ x, BddBelow ((fun y => D.c k i * y + F D k b i y) '' Set.Ioi x) :=
                      fun x => ⟨D.c k i * x, by
                        rintro _ ⟨y, hy, rfl⟩
                        have := mul_le_mul_of_nonneg_left (le_of_lt hy) (hD.c_nonneg k i)
                        linarith [hFnn y]⟩
                    have hmmono : Monotone m := by
                      intro x x' hxx'
                      apply csInf_le_csInf (hmbdd x) ((Set.nonempty_Ioi).image _)
                      exact Set.image_mono (Set.Ioi_subset_Ioi hxx')
                    have heq : ∀ x, sInf (calendarObjective D k b i x '' calendarActions allowed k) =
                        min (F D k b i x) (D.K k i - D.c k i * x + m x) := by
                      intro x
                      have himg : calendarObjective D k b i x '' Set.Ioi 0 =
                          (fun t => D.K k i - D.c k i * x + t) ''
                            ((fun y => D.c k i * y + F D k b i y) '' Set.Ioi x) := by
                        rw [show Set.Ioi x = (fun u => x + u) '' Set.Ioi 0 by
                          rw [Set.image_const_add_Ioi, add_zero]]
                        rw [Set.image_image, Set.image_image]
                        apply Set.image_congr
                        intro u hu
                        have hu' : (0:ℝ) < u := hu
                        simp only [calendarObjective, orderCost, delta, hu', if_true]; ring
                      have hne : (calendarObjective D k b i x '' Set.Ioi 0).Nonempty :=
                        (Set.nonempty_Ioi).image _
                      have hbd : BddBelow (calendarObjective D k b i x '' Set.Ioi 0) :=
                        ⟨0, by rintro _ ⟨u, hu, rfl⟩; exact hobjnn x u (le_of_lt hu)⟩
                      rw [hact, Set.image_insert_eq, csInf_insert hbd hne, h0]
                      congr 1
                      rw [himg, ← Monotone.map_csInf_of_continuousAt (f := fun t => D.K k i - D.c k i * x + t)
                        (continuous_add_left _).continuousAt
                        (fun a b h => by dsimp only; linarith) ((Set.nonempty_Ioi).image _) (hmbdd x)]
                    have : (fun x => sInf (calendarObjective D k b i x '' calendarActions allowed k)) =
                        fun x => min (F D k b i x) (D.K k i - D.c k i * x + m x) := funext heq
                    rw [this]
                    exact (hFmeas b hbm k i).min
                      ((measurable_const.sub (measurable_const.mul measurable_id)).add hmmono.measurable)
                  · have hact : calendarActions allowed k = {0} := by
                      ext u
                      simp only [calendarActions, ha, not_false_eq_true, true_implies, Set.mem_setOf_eq,
                        Set.mem_singleton_iff]
                      exact ⟨fun h => h.2, fun h => ⟨h ▸ le_rfl, h⟩⟩
                    simp only [hact, Set.image_singleton, csInf_singleton, h0]
                    exact hFmeas b hbm k i
                · calc _ ≤ calendarObjective D k b i x 0 :=
                        csInf_le (hbdd x) ⟨0, ⟨le_rfl, fun _ => rfl⟩, rfl⟩
                    _ = F D k b i x := h0 x
                    _ ≤ _ := hFle x
              have hgood : ∀ m, (∀ j, Measurable (calendarAux D allowed N m j)) ∧
                  ∃ C, 0 ≤ C ∧ ∀ j x, calendarAux D allowed N m j x ≤ C * (1 + |x|) := by
                intro m
                induction m with
                | zero =>
                  refine ⟨fun j => ?_, D.C, hD.C_pos.le, fun j x => hD.f_growth _ _ _⟩
                  have := (hD.f_convex N j).continuousOn_interior
                  rw [interior_univ] at this
                  exact (continuousOn_univ.mp this).measurable
                | succ m ih =>
                  obtain ⟨hm, C, hC, hCb⟩ := ih
                  have hnn : ∀ j x, 0 ≤ calendarAux D allowed N m j x := hAuxnn m
                  have hs := hstep _ C hC hm hnn hCb (N - (m + 1))
                  refine ⟨fun j => ?_, D.C + C + C * |D.M|,
                    add_nonneg (add_nonneg hD.C_pos.le hC) (mul_nonneg hC (abs_nonneg _)), fun j x => ?_⟩
                  · have hf := (hD.f_convex (N - (m+1)) j).continuousOn_interior
                    rw [interior_univ] at hf
                    exact (continuousOn_univ.mp hf).measurable.add (hs j).1
                  · simp only [calendarAux]
                    have h1 := hD.f_growth (N - (m+1)) j x
                    have h2 := (hs j).2 x
                    have h3 : C * D.M ≤ C * |D.M| * (1 + |x|) := by
                      have := mul_le_mul_of_nonneg_left (le_abs_self D.M) hC
                      have : 0 ≤ C * |D.M| * |x| := by positivity
                      nlinarith
                    nlinarith
              refine ⟨fun n hn i j y => ?_, fun m j => ?_⟩
              · obtain ⟨hm, C, hC, hCb⟩ := hgood (N - (n + 1))
                exact (hIntGen _ C hC hm (fun j x => hVnn (n+1) j x) hCb n i j y).1
              · obtain ⟨_, C, hC, hCb⟩ := hgood m
                exact ⟨C, hC, hCb j⟩
            have hInt := hIntB.1
            have hKadd : ∀ (K1 K2 : ℝ) (h q : ℝ → ℝ), BertsekasKConvex K1 h → BertsekasKConvex K2 q →
                BertsekasKConvex (K1 + K2) (fun x => h x + q x) := by
              intro K1 K2 h q h1 h2 z b y hz hb
              have e1 := h1 z b y hz hb
              have e2 := h2 z b y hz hb
              have e : z / b * ((h y + q y) - (h (y - b) + q (y - b))) =
                  z / b * (h y - h (y - b)) + z / b * (q y - q (y - b)) := by ring
              simp only
              rw [e]; linarith
            have hKmono : ∀ (K1 K2 : ℝ) (h : ℝ → ℝ), K1 ≤ K2 → BertsekasKConvex K1 h →
                BertsekasKConvex K2 h := by
              intro K1 K2 h hle h1 z b y hz hb
              have := h1 z b y hz hb; linarith
            have hKconv : ∀ (f : ℝ → ℝ), ConvexOn ℝ Set.univ f → BertsekasKConvex 0 f := by
              intro f hf z b y hz hb
              rcases hz.eq_or_lt with h0 | hpos
              · subst h0; simp
              have hsl := hf.slope_mono_adjacent (Set.mem_univ (y - b)) (Set.mem_univ (y + z))
                (by linarith : y - b < y) (by linarith : y < y + z)
              rw [show y - (y - b) = b by ring, show y + z - y = z by ring] at hsl
              have h1 : z / b * (f y - f (y - b)) = z * ((f y - f (y - b)) / b) := by ring
              have h2 : z * ((f (y + z) - f y) / z) = f (y + z) - f y := by field_simp
              have h3 := mul_le_mul_of_nonneg_left hsl hpos.le
              rw [add_comm z y]; linarith
            have hKlin : ∀ (c : ℝ), BertsekasKConvex 0 (fun x => - (c * x)) := by
              intro c z b y hz hb
              have : z / b * (-(c * y) - -(c * (y - b))) = - (c * z) := by field_simp; ring
              simp only; rw [this]; ring_nf; rfl
            have hfcont : ∀ k j, Continuous (D.f k j) := by
              intro k j
              have hf := (hD.f_convex k j).continuousOn_interior
              rw [interior_univ] at hf
              exact continuousOn_univ.mp hf
            have hcore : ∀ n < N, (∀ j, Continuous (V (n+1) j) ∧ BertsekasKConvex (D.K (n+1) j) (V (n+1) j)) →
                ∀ i, ∃ p : EReal × EReal, p.1 ≤ p.2 ∧ p.2 ≠ ⊤ ∧ (p.1 ≠ ⊥ → p.2 ≠ ⊥) ∧
                (∀ x, ∀ u ∈ calendarActions allowed n,
                  calendarObjective D n (V (n+1)) i x (if allowed n then orderSS p.1 p.2 x else 0) ≤
                  calendarObjective D n (V (n+1)) i x u) ∧
                Continuous (fun x => calendarObjective D n (V (n+1)) i x
                  (if allowed n then orderSS p.1 p.2 x else 0) + D.c n i * x) ∧
                BertsekasKConvex (D.K n i) (fun x => calendarObjective D n (V (n+1)) i x
                  (if allowed n then orderSS p.1 p.2 x else 0) + D.c n i * x) := by
              intro n hn hQ i
              set g : ℝ → ℝ := fun y => D.c n i * y + F D n (V (n+1)) i y with hg
              have hK : 0 ≤ D.K n i := hD.K_nonneg n i
              have hVcg : ∀ j, Continuous (V (n+1) j) ∧ ∃ C, 0 ≤ C ∧ ∀ x, V (n+1) j x ≤ C * (1 + |x|) := by
                intro j
                obtain ⟨C, hC, hCb⟩ := hIntB.2 (N - (n+1)) j
                exact ⟨(hQ j).1, C, hC, hCb⟩
              have hg_cont : Continuous g := by
                have hφI0 : Integrable (D.φ n i) :=
                  Integrable.of_integral_ne_zero (by rw [hD.φ_int]; norm_num)
                have hFc : ∀ j, Continuous (fun y => ∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) := by
                  intro j
                  obtain ⟨hc, C, hC, hCb⟩ := hVcg j
                  refine continuous_iff_continuousAt.mpr fun y0 => ?_
                  refine continuousAt_of_dominated
                    (bound := fun w => C * (1 + |y0| + 1) * D.φ n i w + C * (w * D.φ n i w)) ?_ ?_ ?_ ?_
                  · exact Eventually.of_forall fun y => ((hc.comp (continuous_const.sub continuous_id)).measurable.mul
                      (hD.φ_meas n i)).aestronglyMeasurable
                  · filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
                    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
                    have hw0 : (0:ℝ) < w := hw
                    rw [Metric.mem_ball, Real.dist_eq] at hy
                    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hVnn _ _ _) (hD.φ_nonneg _ _ _))]
                    have h1 := hCb (y - w)
                    have h2 : |y - w| ≤ |y0| + 1 + w := by
                      have := abs_sub y w
                      rw [abs_of_pos hw0] at this
                      have : |y| ≤ |y0| + 1 := by
                        have := abs_sub_abs_le_abs_sub y y0; linarith
                      linarith
                    have hφ := hD.φ_nonneg n i w
                    have h3 : C * (1 + |y - w|) ≤ C * (1 + |y0| + 1 + w) := by
                      apply mul_le_mul_of_nonneg_left _ hC; linarith
                    have := mul_le_mul_of_nonneg_right (h1.trans h3) hφ
                    nlinarith [this]
                  · exact ((hφI0.const_mul _).add ((hD.mean_integrable n i).const_mul _)).restrict
                  · exact Eventually.of_forall fun w =>
                      ((hc.comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt
                simp only [hg, F]
                exact (continuous_const.mul continuous_id).add
                  (continuous_finset_sum _ fun j _ => continuous_const.mul (hFc j))
              have hVK : ∀ j, BertsekasKConvex (D.K (n+1) j) (V (n+1) j) := fun j => (hQ j).2
              have hφI0 : Integrable (D.φ n i) :=
                Integrable.of_integral_ne_zero (by rw [hD.φ_int]; norm_num)
              have hφle : ∫ w in Set.Ioi 0, D.φ n i w ≤ 1 := by
                rw [← hD.φ_int n i]
                exact setIntegral_le_integral hφI0 (Eventually.of_forall (hD.φ_nonneg n i))
              have hIj : ∀ j (z b y : ℝ), 0 ≤ z → 0 < b →
                  (∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) + (z / b) *
                    ((∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) -
                      ∫ w in Set.Ioi 0, V (n+1) j (y - b - w) * D.φ n i w) ≤
                  D.K (n+1) j + ∫ w in Set.Ioi 0, V (n+1) j (z + y - w) * D.φ n i w := by
                intro j z b y hz hb
                have hA := hInt n hn i j y
                have hB := hInt n hn i j (y - b)
                have hC := hInt n hn i j (z + y)
                have hφI : Integrable (D.φ n i) (volume.restrict (Set.Ioi 0)) := hφI0.restrict
                calc _ = ∫ w in Set.Ioi 0, (V (n+1) j (y - w) * D.φ n i w + (z / b) *
                        (V (n+1) j (y - w) * D.φ n i w - V (n+1) j (y - b - w) * D.φ n i w)) := by
                        have := integral_add hA ((hA.sub hB).const_mul (z / b))
                        simp only [Pi.sub_apply] at this
                        rw [this, integral_const_mul, integral_sub hA hB]
                  _ ≤ ∫ w in Set.Ioi 0, (D.K (n+1) j * D.φ n i w + V (n+1) j (z + y - w) * D.φ n i w) := by
                        refine integral_mono (hA.add ((hA.sub hB).const_mul _))
                          ((hφI.const_mul _).add hC) fun w => ?_
                        have h := hVK j z b (y - w) hz hb
                        rw [show y - w - b = y - b - w by ring, show z + (y - w) = z + y - w by ring] at h
                        have hφ := hD.φ_nonneg n i w
                        have := mul_le_mul_of_nonneg_right h hφ
                        dsimp only
                        nlinarith [this]
                  _ = D.K (n+1) j * (∫ w in Set.Ioi 0, D.φ n i w) +
                        ∫ w in Set.Ioi 0, V (n+1) j (z + y - w) * D.φ n i w := by
                        rw [integral_add (hφI.const_mul _) hC, integral_const_mul]
                  _ ≤ _ := by
                        have := mul_le_mul_of_nonneg_left hφle (hD.K_nonneg (n+1) j)
                        linarith
              have hg_K : ∀ z b y : ℝ, 0 ≤ z → 0 < b →
                  g y + (z / b) * (g y - g (y - b)) ≤ D.K n i + g (z + y) := by
                intro z b y hz hb
                simp only [hg, F]
                have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
                  mul_le_mul_of_nonneg_left (hIj j z b y hz hb) (hD.P_nonneg i j)
                have e1 : ∑ j, D.P i j * ((∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) + (z / b) *
                    ((∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) -
                      ∫ w in Set.Ioi 0, V (n+1) j (y - b - w) * D.φ n i w)) =
                    (∑ j, D.P i j * ∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) + (z / b) *
                    ((∑ j, D.P i j * ∫ w in Set.Ioi 0, V (n+1) j (y - w) * D.φ n i w) -
                      ∑ j, D.P i j * ∫ w in Set.Ioi 0, V (n+1) j (y - b - w) * D.φ n i w) := by
                  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun j _ => by ring
                have e2 : ∑ j, D.P i j * (D.K (n+1) j + ∫ w in Set.Ioi 0, V (n+1) j (z + y - w) * D.φ n i w) =
                    (∑ j, D.P i j * D.K (n+1) j) +
                      ∑ j, D.P i j * ∫ w in Set.Ioi 0, V (n+1) j (z + y - w) * D.φ n i w := by
                  rw [← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun j _ => by ring
                have h41' := (h41 n hn i).1
                have hc : z / b * (D.c n i * y - D.c n i * (y - b)) = D.c n i * z := by
                  field_simp; ring
                rw [e1, e2] at hsum
                nlinarith [hsum, h41', hc]
              have hVf : ∀ j y, D.f (n+1) j y ≤ V (n+1) j y := by
                intro j y
                rcases lt_or_eq_of_le (Nat.succ_le_of_lt hn) with h | h
                · rw [hVsucc (n+1) h j y]
                  have : 0 ≤ sInf (calendarObjective D (n+1) (V (n+1+1)) j y ''
                      calendarActions allowed (n+1)) :=
                    Real.sInf_nonneg (by rintro _ ⟨u, hu, rfl⟩; exact hobj_nn _ _ _ _ hu.1)
                  linarith
                · have h' : n + 1 = N := h
                  rw [h', hVN]
              have hg_top : Tendsto g atTop atTop := by
                refine tendsto_atTop_mono (fun y => ?_) (h42 n hn i)
                simp only [hg]
                have : F D n (D.f (n+1)) i y ≤ F D n (V (n+1)) i y := by
                  unfold F
                  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hD.P_nonneg _ _)
                  have hfm : Measurable (D.f (n+1) j) := by
                    have hf := (hD.f_convex (n+1) j).continuousOn_interior
                    rw [interior_univ] at hf
                    exact (continuousOn_univ.mp hf).measurable
                  have hfI : Integrable (fun z => D.f (n+1) j (y - z) * D.φ n i z)
                      (volume.restrict (Set.Ioi 0)) := by
                    refine (hInt n hn i j y).mono'
                      ((hfm.comp (measurable_const.sub measurable_id)).mul
                        (hD.φ_meas n i)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
                    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hD.f_nonneg _ _ _) (hD.φ_nonneg _ _ _))]
                    exact mul_le_mul_of_nonneg_right (hVf j _) (hD.φ_nonneg _ _ _)
                  exact integral_mono hfI (hInt n hn i j y)
                    (fun z => mul_le_mul_of_nonneg_right (hVf j _) (hD.φ_nonneg _ _ _))
                linarith
              have hobj : ∀ x u, calendarObjective D n (V (n+1)) i x u =
                  D.K n i * delta u + g (x + u) - D.c n i * x := by
                intro x u; simp only [calendarObjective, orderCost, hg]; ring
              have hkey : ∀ x x' y, x' < x → g x' ≤ g x → x ≤ y → g x ≤ D.K n i + g y := by
                intro x x' y hx' hgx hxy
                have h := hg_K (y - x) (x - x') x (by linarith) (by linarith)
                rw [show x - (x - x') = x' by ring, show y - x + x = y by ring] at h
                have : 0 ≤ (y - x) / (x - x') * (g x - g x') :=
                  mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
                linarith
              have hδpos : ∀ u : ℝ, 0 < u → delta u = 1 := fun u hu => by simp [delta, hu]
              have hδ0 : delta 0 = 0 := by simp [delta]
              have hg0 : ∀ x, calendarObjective D n (V (n+1)) i x 0 + D.c n i * x = g x := by
                intro x; rw [hobj, hδ0]; simp
              by_cases ha : allowed n
              swap
              · refine ⟨(⊥, ⊥), le_rfl, bot_ne_top, fun h => absurd rfl h, fun x u hu => ?_, ?_, ?_⟩
                · rw [if_neg ha, hu.2 ha]
                · simp only [if_neg ha, hg0]; exact hg_cont
                · simp only [if_neg ha, hg0]; exact hg_K
              simp only [if_pos ha]
              by_cases hmin : ∃ S0, ∀ y, g S0 ≤ g y
              · obtain ⟨S0, hS0⟩ := hmin
                let T : Set ℝ := {x | x ≤ S0 ∧ g x ≤ D.K n i + g S0}
                have hS0T : S0 ∈ T := ⟨le_rfl, by linarith⟩
                let s : EReal := sInf ((fun x : ℝ => (x : EReal)) '' T)
                have hsS : s ≤ (S0 : EReal) := sInf_le ⟨S0, hS0T, rfl⟩
                have hopt : ∀ x, ∀ u ∈ calendarActions allowed n,
                    calendarObjective D n (V (n+1)) i x (orderSS s (S0 : EReal) x) ≤
                    calendarObjective D n (V (n+1)) i x u := by
                  intro x u hu
                  simp only [hobj, orderSS, EReal.toReal_coe]
                  split_ifs with hxs
                  · have hxS : x < S0 := EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hxs hsS)
                    rw [hδpos _ (by linarith), show x + (S0 - x) = S0 by ring]
                    have hxT : x ∉ T := fun hxT =>
                      absurd (sInf_le ⟨x, hxT, rfl⟩ : s ≤ x) (not_le.mpr hxs)
                    rcases hu.1.eq_or_lt with h0 | hpos
                    · rw [← h0, hδ0, add_zero]
                      have : ¬ g x ≤ D.K n i + g S0 := fun h => hxT ⟨hxS.le, h⟩
                      linarith
                    · rw [hδpos _ hpos]; linarith [hS0 (x+u)]
                  · rw [hδ0, add_zero, mul_zero, zero_add]
                    rcases hu.1.eq_or_lt with h0 | hpos
                    · rw [← h0, hδ0, add_zero, mul_zero, zero_add]
                    rw [hδpos _ hpos, mul_one]
                    suffices g x ≤ D.K n i + g (x+u) by linarith
                    rcases lt_or_ge S0 x with hSx | hxS
                    · exact hkey x S0 (x+u) hSx (hS0 x) (by linarith)
                    · suffices g x ≤ D.K n i + g S0 by linarith [hS0 (x+u)]
                      by_contra hcon
                      push_neg at hcon
                      rcases hxS.eq_or_lt with hxe | hxlt
                      · rw [hxe] at hcon; linarith
                      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
                        (isOpen_lt continuous_const hg_cont) x hcon
                      have hsx : s ≤ (x : EReal) := not_lt.mp hxs
                      have hlt : s < ((x + ε : ℝ) : EReal) :=
                        lt_of_le_of_lt hsx (EReal.coe_lt_coe_iff.mpr (by linarith))
                      obtain ⟨_, ⟨t, htT, rfl⟩, htlt⟩ := sInf_lt_iff.mp hlt
                      have htlt' : t < x + ε := EReal.coe_lt_coe_iff.mp htlt
                      have htx : t ≤ x - ε := by
                        by_contra h
                        push_neg at h
                        have : t ∈ Metric.ball x ε := by
                          rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
                        have := hball this
                        simp only [Set.mem_setOf_eq] at this
                        linarith [htT.2]
                      have h := hg_K (S0 - x) (x - t) x (by linarith) (by linarith)
                      rw [show x - (x - t) = t by ring, show S0 - x + x = S0 by ring] at h
                      have : 0 ≤ (S0 - x) / (x - t) * (g x - g t) :=
                        mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith [htT.2])
                      linarith
                have hC : ∀ x : ℝ, s ≤ (x : EReal) → ∀ y : ℝ, x ≤ y → g x ≤ D.K n i + g y := by
                  intro x hsx y hxy
                  have h0 : orderSS s (S0 : EReal) x = 0 := by simp [orderSS, not_lt.mpr hsx]
                  rcases hxy.eq_or_lt with he | hlt
                  · rw [he]; linarith
                  have := hopt x (y - x) ⟨by linarith, fun h => absurd ha h⟩
                  rw [h0, hobj, hobj, hδ0, hδpos _ (by linarith), show x + (y - x) = y by ring] at this
                  simp at this; linarith
                have hrepr : (fun x : ℝ => calendarObjective D n (V (n+1)) i x (orderSS s (S0 : EReal) x) +
                    D.c n i * x) = fun x : ℝ => if (x : EReal) < s then D.K n i + g S0 else g x := by
                  funext x
                  simp only [hobj, orderSS, EReal.toReal_coe]
                  split_ifs with hxs
                  · have hxS : x < S0 := EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hxs hsS)
                    rw [hδpos _ (by linarith), show x + (S0 - x) = S0 by ring]; ring
                  · rw [hδ0]; ring
                have hcK : Continuous (fun x : ℝ => if (x : EReal) < s then D.K n i + g S0 else g x) ∧
                    BertsekasKConvex (D.K n i) (fun x : ℝ => if (x : EReal) < s then D.K n i + g S0 else g x) := by
                  by_cases hsb : s = ⊥
                  · simp only [hsb, not_lt_bot, if_false]; exact ⟨hg_cont, hg_K⟩
                  have hs0 : s = ((s.toReal : ℝ) : EReal) :=
                    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top S0) hsS) hsb).symm
                  set s0 := s.toReal
                  have hs0S : s0 ≤ S0 := EReal.coe_le_coe_iff.mp (hs0 ▸ hsS)
                  have hA : ∀ x, x < s0 → D.K n i + g S0 < g x := by
                    intro x hx
                    have hxS : x < S0 := by linarith
                    by_contra hcon; push_neg at hcon
                    have : s ≤ (x : EReal) := sInf_le ⟨x, ⟨hxS.le, hcon⟩, rfl⟩
                    rw [hs0] at this
                    exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr hx)
                  have hCs : ∀ x, s0 ≤ x → ∀ y, x ≤ y → g x ≤ D.K n i + g y := fun x hx =>
                    hC x (by rw [hs0]; exact EReal.coe_le_coe_iff.mpr hx)
                  have hgs0 : g s0 = D.K n i + g S0 := by
                    apply le_antisymm (hCs s0 le_rfl S0 hs0S)
                    exact ge_of_tendsto (hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
                      (eventually_nhdsWithin_of_forall (s := Set.Iio s0) fun x hx => (hA x hx).le)
                  rw [hs0]
                  simp only [EReal.coe_lt_coe_iff]
                  constructor
                  · refine Continuous.if ?_ continuous_const hg_cont
                    intro a ha
                    rw [show {x : ℝ | x < s0} = Set.Iio s0 from rfl, frontier_Iio] at ha
                    rw [Set.mem_singleton_iff.mp ha, hgs0]
                  · intro z b y hz hb
                    simp only
                    have hgmin : ∀ w, g S0 ≤ (if w < s0 then D.K n i + g S0 else g w) := by
                      intro w; split_ifs
                      · linarith
                      · exact hS0 w
                    by_cases hy : y < s0
                    · have hyb : y - b < s0 := by linarith
                      rw [if_pos hy, if_pos hyb]; simp only [sub_self, mul_zero, add_zero]
                      linarith [hgmin (z + y)]
                    · push_neg at hy
                      have hyz : ¬ (z + y < s0) := by linarith
                      rw [if_neg (not_lt.mpr hy), if_neg hyz]
                      by_cases hyb : y - b < s0
                      · rw [if_pos hyb]
                        have h1 := hCs y hy (z+y) (by linarith)
                        by_cases hle : g y ≤ D.K n i + g S0
                        · have : z / b * (g y - (D.K n i + g S0)) ≤ 0 :=
                            mul_nonpos_of_nonneg_of_nonpos (div_nonneg hz hb.le) (by linarith)
                          linarith
                        · push_neg at hle
                          have hyS : S0 < y := by
                            by_contra h; push_neg at h; linarith [hCs y hy S0 h]
                          have h2 := hg_K z (y - S0) y hz (by linarith)
                          rw [show y - (y - S0) = S0 by ring] at h2
                          have h3 : z / b ≤ z / (y - S0) :=
                            div_le_div_of_nonneg_left hz (by linarith) (by linarith)
                          have h4 : z / b * (g y - (D.K n i + g S0)) ≤ z / (y - S0) * (g y - g S0) := by
                            calc _ ≤ z / (y - S0) * (g y - (D.K n i + g S0)) :=
                                  mul_le_mul_of_nonneg_right h3 (by linarith)
                              _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hz (by linarith))
                          linarith
                      · rw [if_neg hyb]; exact hg_K z b y hz hb
                refine ⟨(s, (S0 : EReal)), hsS, EReal.coe_ne_top _, fun _ => EReal.coe_ne_bot _,
                  hopt, ?_, ?_⟩
                · rw [hrepr]; exact hcK.1
                · rw [hrepr]; exact hcK.2
              · push_neg at hmin
                refine ⟨(⊥, ⊥), le_rfl, bot_ne_top, fun h => absurd rfl h, ?_, ?_, ?_⟩
                on_goal 2 => simp only [orderSS, not_lt_bot, if_false, hg0]; exact hg_cont
                on_goal 2 => simp only [orderSS, not_lt_bot, if_false, hg0]; exact hg_K
                intro x u hu
                simp only [hobj, orderSS, not_lt_bot, if_false]
                rcases hu.1.eq_or_lt with h0 | hpos
                · rw [← h0]
                rw [hδ0, hδpos _ hpos, mul_zero, mul_one, add_zero]
                suffices g x ≤ D.K n i + g (x+u) by linarith
                have hex : ∃ x' < x, g x' ≤ g x := by
                  by_contra hno
                  push_neg at hno
                  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hg_top.eventually_ge_atTop (g x + 1))
                  obtain ⟨w, hw, hwmin⟩ := (isCompact_Icc (a := x) (b := max x R)).exists_isMinOn
                    (Set.nonempty_Icc.mpr (le_max_left _ _)) hg_cont.continuousOn
                  obtain ⟨y, hy⟩ := hmin w
                  have hgw : g w ≤ g x := isMinOn_iff.mp hwmin x ⟨le_rfl, le_max_left _ _⟩
                  rcases lt_or_ge y x with hyx | hyx
                  · linarith [hno y hyx]
                  rcases le_or_gt y (max x R) with hyR | hyR
                  · linarith [isMinOn_iff.mp hwmin y ⟨hyx, hyR⟩]
                  · linarith [hR y (le_trans (le_max_right _ _) hyR.le)]
                obtain ⟨x', hx', hgx'⟩ := hex
                exact hkey x x' (x+u) hx' hgx' (by linarith)
            have hQ : ∀ m, m ≤ N → ∀ j, Continuous (V (N - m) j) ∧ BertsekasKConvex (D.K (N - m) j) (V (N - m) j) := by
              intro m
              induction m with
              | zero =>
                intro _ j
                have hVN' : V (N - 0) j = D.f N j := by funext x; simp only [Nat.sub_zero]; exact hVN j x
                rw [hVN', Nat.sub_zero]
                exact ⟨hfcont N j, hKmono 0 _ _ (hD.K_nonneg N j) (hKconv _ (hD.f_convex N j))⟩
              | succ m ih =>
                intro hm j
                have hn : N - (m+1) < N := by omega
                have hQ1 : ∀ j, Continuous (V (N - (m+1) + 1) j) ∧
                    BertsekasKConvex (D.K (N - (m+1) + 1) j) (V (N - (m+1) + 1) j) := by
                  rw [show N - (m+1) + 1 = N - m by omega]; exact ih (by omega)
                obtain ⟨p, hp1, hp2, -, hopt, hc, hk⟩ := hcore (N - (m+1)) hn hQ1 j
                set n := N - (m+1) with hndef
                have hrep : V n j = fun x => (D.f n j x + - (D.c n j * x)) +
                    (calendarObjective D n (V (n+1)) j x (if allowed n then orderSS p.1 p.2 x else 0) +
                      D.c n j * x) := by
                  funext x
                  rw [hVsucc n hn j x]
                  have hleast : IsLeast (calendarObjective D n (V (n + 1)) j x '' calendarActions allowed n)
                      (calendarObjective D n (V (n+1)) j x (if allowed n then orderSS p.1 p.2 x else 0)) := by
                    refine ⟨Set.mem_image_of_mem _ ?_, ?_⟩
                    · refine ⟨?_, fun hna => by simp [hna]⟩
                      split_ifs
                      · unfold orderSS; split_ifs with h
                        · have hb' : p.2 ≠ ⊥ := ne_bot_of_gt (lt_of_lt_of_le h hp1)
                          have : (x : EReal) < (p.2.toReal : EReal) := by
                            rw [EReal.coe_toReal hp2 hb']; exact lt_of_lt_of_le h hp1
                          have := EReal.coe_lt_coe_iff.mp this; linarith
                        · exact le_rfl
                      · exact le_rfl
                    · rintro _ ⟨u, hu, rfl⟩
                      exact hopt x u hu
                  rw [hleast.csInf_eq]; ring
                rw [hrep]
                refine ⟨((hfcont n j).add (continuous_const.mul continuous_id).neg).add hc, ?_⟩
                have := hKadd 0 (D.K n j) _ _
                  (by simpa using hKadd 0 0 _ _ (hKconv _ (hD.f_convex n j)) (hKlin (D.c n j))) hk
                simpa using this
            have hQ' : ∀ n (h : n < N), ∀ j, Continuous (V (n+1) j) ∧ BertsekasKConvex (D.K (n+1) j) (V (n+1) j) := by
              intro n h
              have := hQ (N - (n+1)) (by omega)
              rwa [show N - (N - (n+1)) = n + 1 by omega] at this
            let s : ℕ → Fin L → EReal := fun n i => if h : n < N then (Classical.choose (hcore n h (hQ' n h) i)).1 else ⊥
            let S : ℕ → Fin L → EReal := fun n i => if h : n < N then (Classical.choose (hcore n h (hQ' n h) i)).2 else ⊥
            have hsS : ∀ n < N, ∀ i, (s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
                ∀ x, ∀ u ∈ calendarActions allowed n,
                  calendarObjective D n (V (n+1)) i x (calendarRule allowed s S n i x) ≤
                  calendarObjective D n (V (n+1)) i x u := by
              intro n hn i
              have := Classical.choose_spec (hcore n hn (hQ' n hn) i)
              simp only [s, S, hn, dif_pos, calendarRule]
              exact ⟨⟨this.1, this.2.1, this.2.2.1⟩, this.2.2.2.1⟩
            have hSS_nn : ∀ (a b : EReal), a ≤ b → b ≠ ⊤ → ∀ x, 0 ≤ orderSS a b x := by
              intro a b hab hb x
              unfold orderSS
              split_ifs with h
              · have hb' : b ≠ ⊥ := ne_bot_of_gt (lt_of_lt_of_le h hab)
                have : (x : EReal) < (b.toReal : EReal) := by
                  rw [EReal.coe_toReal hb hb']; exact lt_of_lt_of_le h hab
                have := EReal.coe_lt_coe_iff.mp this
                linarith
              · exact le_rfl
            have hrule_nn : ∀ n i x, 0 ≤ calendarRule allowed s S n i x := by
              intro n i x
              unfold calendarRule
              split_ifs with ha
              · by_cases hn : n < N
                · exact hSS_nn _ _ (hsS n hn i).1.1 (hsS n hn i).1.2.1 x
                · simp [s, S, hn, orderSS]
              · exact le_rfl
            have hrule_act : ∀ n i x, calendarRule allowed s S n i x ∈ calendarActions allowed n := by
              intro n i x
              refine ⟨hrule_nn n i x, fun ha => ?_⟩
              simp [calendarRule, ha]
            have hInB0 : ∀ n < N, InB0 (calendarRule allowed s S n) := by
              intro n hn
              refine ⟨fun i x => hrule_nn n i x, fun k i x => if allowed n ∧ s n i ≠ ⊥ then
                max 0 ((S n i).toReal - x) * min 1 (max 0 ((k:ℝ) * ((s n i).toReal - x))) else 0,
                ?_, ?_, ?_⟩
              · intro k i
                dsimp only
                split_ifs
                · fun_prop
                · exact continuous_const
              · intro k i x
                dsimp only
                split_ifs
                · exact mul_nonneg (le_max_left _ _) (le_min zero_le_one (le_max_left _ _))
                · exact le_rfl
              · intro i x
                by_cases h : allowed n ∧ s n i ≠ ⊥
                · simp only [h, and_self, if_true, ne_eq, not_false_eq_true]
                  have hsS' := (hsS n hn i).1
                  have hst : s n i ≠ ⊤ := ne_top_of_le_ne_top hsS'.2.1 hsS'.1
                  have hSb : S n i ≠ ⊥ := hsS'.2.2 h.2
                  set a := (s n i).toReal with ha
                  have hsa : s n i = (a : EReal) := (EReal.coe_toReal hst h.2).symm
                  have hab : a ≤ (S n i).toReal := by
                    have := hsS'.1
                    rw [hsa, ← EReal.coe_toReal hsS'.2.1 hSb] at this
                    exact EReal.coe_le_coe_iff.mp this
                  unfold calendarRule orderSS
                  simp only [h.1, if_true, hsa, EReal.coe_lt_coe_iff]
                  split_ifs with hx
                  · apply tendsto_const_nhds.congr'
                    filter_upwards [eventually_ge_atTop (⌈1 / (a - x)⌉₊)] with k hk
                    have hax : 0 < a - x := sub_pos.mpr hx
                    have hk' : 1 / (a - x) ≤ (k:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
                    have : 1 ≤ (k:ℝ) * (a - x) := by
                      rw [div_le_iff₀ hax] at hk'; linarith
                    rw [max_eq_right (show (0:ℝ) ≤ (k:ℝ) * (a - x) by linarith), min_eq_left this,
                      max_eq_right (show (0:ℝ) ≤ (S n i).toReal - x by linarith)]
                    ring
                  · apply tendsto_const_nhds.congr'
                    filter_upwards with k
                    have : (k:ℝ) * (a - x) ≤ 0 :=
                      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith [not_lt.mp hx])
                    rw [max_eq_left this]; simp
                · simp only [h, if_false]
                  have : calendarRule allowed s S n i x = 0 := by
                    unfold calendarRule orderSS
                    split_ifs with h1 h2
                    · exfalso; apply h; refine ⟨h1, ?_⟩; intro hb; rw [hb] at h2; exact not_lt_bot h2
                    · rfl
                    · rfl
                  rw [this]; exact tendsto_const_nhds
            have hrule_meas : ∀ n i, Measurable (calendarRule allowed s S n i) := by
              intro n i
              unfold calendarRule
              split_ifs
              · unfold orderSS
                refine Measurable.ite ?_ (measurable_const.sub measurable_id) measurable_const
                exact measurableSet_lt measurable_coe_real_ereal measurable_const
              · exact measurable_const
            have hfb_meas : ∀ n x t (σ : Fin (t + 1) → Fin L),
                Measurable (fbSurplus (calendarRule allowed s S) n x t σ) := by
              intro n x t
              induction t with
              | zero => intro σ; exact measurable_const
              | succ t ih =>
                intro σ
                have hinit : Measurable (fun ξ : Fin (t + 1) → ℝ => (Fin.init ξ : Fin t → ℝ)) :=
                  measurable_pi_lambda _ fun j => measurable_pi_apply _
                have h1 := (ih (Fin.init σ)).comp hinit
                exact (h1.add ((hrule_meas _ _).comp h1)).sub (measurable_pi_apply _)
            have hadm : ∀ n x, CalendarAdmissible allowed N n (feedback (calendarRule allowed s S) n x) := by
              intro n x
              refine ⟨fun t _ => ⟨fun σ ξ => hrule_nn _ _ _, fun σ => ?_⟩, fun t _ σ ξ ha => ?_⟩
              · exact (hrule_meas _ _).comp (hfb_meas n x t σ)
              · simp [feedback, calendarRule, ha]
            have hJ : ∀ n ≤ N, ∀ i x,
                CalendarAdmissible allowed N n (feedback (calendarRule allowed s S) n x) ∧
                J D N n i x (feedback (calendarRule allowed s S) n x) = ENNReal.ofReal (V n i x) ∧
                ∀ U : Policy L, CalendarAdmissible allowed N n U → ENNReal.ofReal (V n i x) ≤ J D N n i x U := by
              have hV2' : ∀ n < N, ∀ i x, V n i x = D.f n i x +
                  calendarObjective D n (V (n + 1)) i x (calendarRule allowed s S n i x) := by
                intro n hn i x
                have hleast : IsLeast (calendarObjective D n (V (n + 1)) i x '' calendarActions allowed n)
                    (calendarObjective D n (V (n+1)) i x (calendarRule allowed s S n i x)) := by
                  refine ⟨Set.mem_image_of_mem _ (hrule_act n i x), ?_⟩
                  rintro _ ⟨u, hu, rfl⟩
                  exact (hsS n hn i).2 x u hu
                rw [hVsucc n hn i x, hleast.csInf_eq]
              intro n hn i x
              obtain ⟨h1, h2⟩ := key V hVN hVnn hInt (calendarRule allowed s S) hV2'
                (fun n hn i x => (hsS n hn i).2 x) hadm n hn i x
              exact ⟨hadm n x, h1, h2⟩
            refine ⟨s, S, fun n hn i => (hsS n hn i).1, hInB0, ?_, hInt, ?_⟩
            · intro n hn i x
              have hne : (calendarObjective D n (V (n + 1)) i x '' calendarActions allowed n).Nonempty :=
                ⟨_, Set.mem_image_of_mem _ (hrule_act n i x)⟩
              have hbdd : BddBelow (calendarObjective D n (V (n + 1)) i x '' calendarActions allowed n) := by
                refine ⟨0, ?_⟩
                rintro _ ⟨u, hu, rfl⟩
                exact hobj_nn n i x u hu.1
              have hleast : IsLeast (calendarObjective D n (V (n + 1)) i x '' calendarActions allowed n)
                  (calendarObjective D n (V (n+1)) i x (calendarRule allowed s S n i x)) := by
                refine ⟨Set.mem_image_of_mem _ (hrule_act n i x), ?_⟩
                rintro _ ⟨u, hu, rfl⟩
                exact (hsS n hn i).2 x u hu
              have hV2 : V n i x = D.f n i x +
                  calendarObjective D n (V (n + 1)) i x (calendarRule allowed s S n i x) := by
                rw [hVsucc n hn i x, hleast.csInf_eq]
              refine ⟨hne, hbdd, hrule_act n i x, ?_, hV2, (hsS n hn i).2 x⟩
              have hH : calendarH D allowed N n i x = calendarObjective D n (V (n+1)) i x
                  (calendarRule allowed s S n i x) + D.c n i * x := by
                unfold calendarH
                split_ifs with ha
                · apply IsLeast.csInf_eq
                  constructor
                  · refine ⟨x + calendarRule allowed s S n i x, ?_, ?_⟩
                    · simp only [Set.mem_Ici]; linarith [hrule_nn n i x]
                    · simp only [calendarZ, calendarObjective, orderCost, add_sub_cancel_left]; ring
                  · rintro _ ⟨y, hy, rfl⟩
                    have := (hsS n hn i).2 x (y - x) ⟨sub_nonneg.mpr hy, fun h => absurd ha h⟩
                    simp only [calendarObjective, orderCost, calendarZ] at this ⊢
                    rw [show x + (y - x) = y by ring] at this
                    linarith
                · have : calendarRule allowed s S n i x = 0 := by simp [calendarRule, ha]
                  rw [this]; simp [calendarZ, calendarObjective, orderCost, delta]; ring
              rw [hV2, hH]; ring
            · intro n hn i x
              obtain ⟨h1, h2, h3⟩ := hJ n hn i x
              refine ⟨h1, hVnn n i x, h2, ?_, fun U hU => h2 ▸ h3 U hU⟩
              apply le_antisymm
              · rw [← h2]
                exact iInf₂_le _ h1
              · exact le_iInf₂ fun U hU => h3 U hU
