-- Prove2me | solution 1 for OptStochMatch.Tight.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:40:22.575787+00:00
-- url     : https://prove2.me/submissions/5355c414-0a25-4ba7-b233-02b432655ea6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Machine
import Theorems.Thm_OptStochMatch_Tight_corollary_4_6
import Theorems.Thm_OptStochMatch_Tight_upper_bound_cgpv
import Theorems.Thm_OptStochMatch_Tight_theorem_5_5
import Theorems.Thm_OptStochMatch_Tight_theorem_6_5

namespace AuxThm11

open MeasureTheory ProbabilityTheory Set OptStochMatch.Tight
open scoped NNReal ENNReal BigOperators

lemma strictMono_perm_eq_refl {n : ℕ} (π : Equiv.Perm (Fin n)) (hπ : StrictMono π) :
    π = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro k
  have h1 : k ≤ π k := hπ.id_le k
  have hsymm : StrictMono π.symm := by
    intro a b hab
    by_contra hge
    have hle : π.symm b ≤ π.symm a := le_of_not_gt hge
    have := hπ.monotone hle
    simp only [Equiv.apply_symm_apply] at this
    exact not_lt_of_ge this hab
  have h2 : π k ≤ k := by simpa using hsymm.id_le (π k)
  exact le_antisymm h2 h1

lemma measurableSet_orderedTimes (n : ℕ) : MeasurableSet (orderedTimes n) := by
  unfold orderedTimes
  have h1 : MeasurableSet {t : Fin n → ℝ | StrictMono t} := by
    have heq : {t : Fin n → ℝ | StrictMono t} =
        ⋂ (i : Fin n) (j : Fin n) (_ : i < j), {t : Fin n → ℝ | t i < t j} := by
      ext t; simp [StrictMono]
    rw [heq]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  have h2 : MeasurableSet {t : Fin n → ℝ | ∀ k, t k ∈ Set.Icc (0 : ℝ) 1} := by
    have heq : {t : Fin n → ℝ | ∀ k, t k ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ k : Fin n, (fun t : Fin n → ℝ => t k) ⁻¹' Set.Icc (0 : ℝ) 1 := by
      ext t; simp
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_Icc.preimage (measurable_pi_apply k)
  exact h1.inter h2

lemma volume_orderedTimes_mul_factorial_le_one (n : ℕ) :
    (n.factorial : ℝ≥0∞) * volume (orderedTimes n) ≤ 1 := by
  let φ : Equiv.Perm (Fin n) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun σ t k => t (σ k)
  let E : Equiv.Perm (Fin n) → Set (Fin n → ℝ) :=
    fun σ => φ σ ⁻¹' orderedTimes n
  have hE_meas : ∀ σ, MeasurableSet (E σ) := by
    intro σ
    have hm : Measurable (φ σ) := measurable_pi_iff.mpr fun k => measurable_pi_apply (σ k)
    exact hm (measurableSet_orderedTimes n)
  have hE_vol : ∀ σ, volume (E σ) = volume (orderedTimes n) := by
    intro σ
    have hmp := MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ.symm
    have hfun : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm : (Fin n → ℝ) → (Fin n → ℝ)) = φ σ := by
      ext t k
      simp [φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    change (volume : Measure (Fin n → ℝ)) (φ σ ⁻¹' orderedTimes n) = _
    rw [← hfun]
    exact hmp.measure_preimage (measurableSet_orderedTimes n).nullMeasurableSet
  have hdisj : Pairwise fun σ₁ σ₂ => Disjoint (E σ₁) (E σ₂) := by
    intro σ₁ σ₂ hne
    rw [Set.disjoint_left]
    intro t ht1 ht2
    have hπ : StrictMono (σ₂.trans σ₁.symm) := by
      intro a b hab
      have hlt : t (σ₂ a) < t (σ₂ b) := ht2.1 hab
      by_contra hge
      have hle : t (σ₁ ((σ₂.trans σ₁.symm) b)) ≤ t (σ₁ ((σ₂.trans σ₁.symm) a)) :=
        ht1.1.monotone (le_of_not_gt hge)
      simp only [Equiv.trans_apply] at hle
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hle
      exact not_lt_of_ge hle hlt
    have heq := strictMono_perm_eq_refl _ hπ
    apply hne
    apply Equiv.ext
    intro k
    have := Equiv.congr_fun heq k
    simp only [Equiv.trans_apply, Equiv.refl_apply] at this
    have h2 := congrArg σ₁ this
    simpa using h2.symm
  have hsub : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), E σ) ⊆
      Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨σ, _, hσ⟩ := mem_iUnion₂.mp ht
    intro k _
    have hk := hσ.2 (σ.symm k)
    simpa [φ] using hk
  have hcube : volume (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) = 1 := by
    change Measure.pi (fun _ : Fin n => (volume : Measure ℝ)) _ = 1
    rw [Measure.pi_pi]
    simp [Real.volume_Icc]
  calc
    (n.factorial : ℝ≥0∞) * volume (orderedTimes n)
      = (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) * volume (orderedTimes n) := by
          rw [Fintype.card_perm, Fintype.card_fin]
    _ = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), volume (E σ) := by
          simp [hE_vol]
    _ = volume (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), E σ) :=
          (measure_biUnion_finset (fun _ _ _ _ h => hdisj h) (fun σ _ => hE_meas σ)).symm
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) := measure_mono hsub
    _ = 1 := hcube

lemma poissonExpect_mono {m : ℕ} (lam : Ty m → ℝ≥0)
    {F G : (n : ℕ) → (Fin n → ℝ) → (Fin n → Ty m) → ℝ≥0∞}
    (hFG : ∀ n t s, F n t s ≤ G n t s) :
    poissonExpect lam F ≤ poissonExpect lam G := by
  unfold poissonExpect
  gcongr with n s _ t
  exact hFG n t s

lemma poissonExpect_const_le {m : ℕ} (lam : Ty m → ℝ≥0) (M : ℝ≥0) :
    poissonExpect lam (fun _ _ _ => (M : ℝ≥0∞)) ≤ (M : ℝ≥0∞) := by
  unfold poissonExpect
  let r : ℝ≥0 := ∑ S : Ty m, lam S
  have hr : (r : ℝ) = totalRate lam := by simp [r, totalRate]
  have hterm : ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (-totalRate lam)) *
        ∑ s : Fin n → Ty m, (∏ k, (lam (s k) : ℝ≥0∞)) * ∫⁻ _ in orderedTimes n, (M : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * (M : ℝ≥0∞) := by
    intro n
    have hvol : volume (orderedTimes n) ≤ ((n.factorial : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]
      exact volume_orderedTimes_mul_factorial_le_one n
    have hprod_sum : ∑ s : Fin n → Ty m, ∏ k, (lam (s k) : ℝ≥0∞) =
        ENNReal.ofReal ((r : ℝ) ^ n) := by
      have hp := (Fintype.prod_sum (fun (_ : Fin n) (S : Ty m) => (lam S : ℝ≥0∞))).symm
      rw [hp]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow r.coe_nonneg]
      congr 1
      dsimp [r]
      push_cast
      rw [ENNReal.ofReal_sum_of_nonneg (fun S _ => NNReal.coe_nonneg (lam S))]
      exact Finset.sum_congr rfl fun S _ => by simp
    calc
      ENNReal.ofReal (Real.exp (-totalRate lam)) *
          ∑ s : Fin n → Ty m, (∏ k, (lam (s k) : ℝ≥0∞)) * ∫⁻ _ in orderedTimes n, (M : ℝ≥0∞)
        = ENNReal.ofReal (Real.exp (-(r : ℝ))) *
            ((∑ s : Fin n → Ty m, ∏ k, (lam (s k) : ℝ≥0∞)) * ((M : ℝ≥0∞) * volume (orderedTimes n))) := by
            rw [← hr]
            simp [lintegral_const, Measure.restrict_apply, Finset.sum_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-(r : ℝ))) *
            (ENNReal.ofReal ((r : ℝ) ^ n) * ((M : ℝ≥0∞) * ((n.factorial : ℝ≥0∞))⁻¹)) := by
            gcongr
            exact le_of_eq hprod_sum
      _ = (ENNReal.ofReal (Real.exp (-(r : ℝ))) *
            ENNReal.ofReal ((r : ℝ) ^ n) * ((n.factorial : ℝ≥0∞))⁻¹) * (M : ℝ≥0∞) := by
            ring
      _ = ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * (M : ℝ≥0∞) := by
            congr 1
            rw [div_eq_mul_inv, ENNReal.ofReal_mul (mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg r.coe_nonneg n)),
              ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
              ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr n.factorial_pos), ENNReal.ofReal_natCast]
  have hpois_sum : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)) = 1 := by
    have hp : poissonMeasure r Set.univ = 1 := measure_univ
    simpa [poissonMeasure, Measure.sum_apply_of_countable] using hp
  calc
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-totalRate lam)) *
        ∑ s : Fin n → Ty m, (∏ k, (lam (s k) : ℝ≥0∞)) * ∫⁻ _ in orderedTimes n, (M : ℝ≥0∞))
      ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) * (M : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum hterm
    _ = (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)) * (M : ℝ≥0∞) :=
        ENNReal.tsum_mul_right
    _ = (M : ℝ≥0∞) := by rw [hpois_sum, one_mul]

lemma poissonRun_nodup {m : ℕ} (π : PoissonPolicy m) (u : ℝ) {n : ℕ}
    (t : Fin n → ℝ) (s : Fin n → Ty m) (k : ℕ) :
    ((poissonRun π u t s k).map Prod.snd).Nodup := by
  induction k with
  | zero => simp [poissonRun]
  | succ k ih =>
    unfold poissonRun
    split_ifs with hk
    · cases hdec : π.decide k u (prefixOf t k hk) (prefixOf s k hk) with
      | none => simp [ih]
      | some i =>
        dsimp only
        split_ifs with hi
        · simp [List.nodup_cons, hi.2, ih]
        · exact ih
    · exact ih

lemma algPois_le_m {m : ℕ} (lam : Ty m → ℝ≥0) (π : PoissonPolicy m) :
    algPois lam π ≤ (m : ℝ) := by
  unfold algPois
  have hlen : ∀ (u : ℝ) (n : ℕ) (t : Fin n → ℝ) (s : Fin n → Ty m),
      ((poissonRun π u t s n).length : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    intro u n t s
    have hnd := (poissonRun_nodup π u t s n).length_le_card
    simp only [List.length_map, Fintype.card_fin] at hnd
    exact Nat.cast_le.mpr hnd
  have hp : ∀ u, poissonExpect lam (fun n t s => ((poissonRun π u t s n).length : ℝ≥0∞)) ≤
      ((m : ℝ≥0) : ℝ≥0∞) :=
    fun u => (poissonExpect_mono lam (hlen u)).trans (poissonExpect_const_le lam m)
  have hseed : seedLaw Set.univ = 1 := by
    simp [seedLaw, Real.volume_Icc]
  have hint : (∫⁻ u, poissonExpect lam (fun n t s => ((poissonRun π u t s n).length : ℝ≥0∞)) ∂seedLaw) ≤
      (m : ℝ≥0∞) := by
    calc
      _ ≤ ∫⁻ _, ((m : ℝ≥0) : ℝ≥0∞) ∂seedLaw := lintegral_mono hp
      _ = ((m : ℝ≥0) : ℝ≥0∞) * seedLaw Set.univ := lintegral_const _
      _ = (m : ℝ≥0∞) := by rw [hseed, mul_one]; simp
  exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg m) (by simpa using hint)

lemma optPois_bddAbove {m : ℕ} (N : Ty m → ℕ) :
    (m : ℝ) ∈ upperBounds {v : ℝ | ∃ x : Fin m → Ty m → ℝ,
      (∀ i S, 0 ≤ x i S ∧ x i S ≤ 1) ∧
      (∀ S : Ty m, ∑ i ∈ S, x i S ≤ (N S : ℝ)) ∧
      (∀ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S ≤ 1) ∧
      v = ∑ S : Ty m, ∑ i ∈ S, x i S} := by
  rintro v ⟨x, _, _, hxi, rfl⟩
  have hswap : ∑ S : Ty m, ∑ i ∈ S, x i S =
      ∑ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S := by
    trans ∑ S : Ty m, ∑ i : Fin m, if i ∈ S then x i S else 0
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
  rw [hswap]
  calc
    ∑ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S
      ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => hxi i
    _ = (m : ℝ) := by simp

lemma optPois_le_m {m : ℕ} (N : Ty m → ℕ) : optPois N ≤ (m : ℝ) := by
  unfold optPois
  refine csSup_le ?_ (optPois_bddAbove N)
  exact ⟨0, 0, ⟨fun _ _ => ⟨le_rfl, zero_le_one⟩, fun S => by simp, fun i => by simp, by simp⟩⟩

lemma exists_pos_optPoisModel : ∃ (m : ℕ) (lam : Ty m → ℝ≥0), 0 < optPoisModel lam := by
  let S₀ : Ty 1 := Finset.univ
  let lam : Ty 1 → ℝ≥0 := fun S => if S = S₀ then 1 else 0
  refine ⟨1, lam, ?_⟩
  unfold optPoisModel
  have hfin : poissonExpect lam (fun _ _ s => ENNReal.ofReal (optPois (typeCounts s))) ≤ 1 := by
    refine (poissonExpect_mono lam fun _ _ s => ?_).trans (poissonExpect_const_le lam 1)
    have hle := optPois_le_m (typeCounts s)
    simpa using ENNReal.ofReal_le_ofReal hle
  have hpos : 0 < poissonExpect lam (fun _ _ s => ENNReal.ofReal (optPois (typeCounts s))) := by
    unfold poissonExpect
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 1)
    let s₁ : Fin 1 → Ty 1 := fun _ => S₀
    have hopt1 : (1 : ℝ) ≤ optPois (typeCounts s₁) := by
      unfold optPois
      refine le_csSup ⟨(1 : ℕ), optPois_bddAbove (typeCounts s₁)⟩ ?_
      let x₀ : Fin 1 → Ty 1 → ℝ := fun _ S => if S = S₀ then 1 else 0
      refine ⟨x₀, ?_, ?_, ?_, ?_⟩
      · intro _ S
        dsimp [x₀]
        split_ifs <;> norm_num
      · intro S
        dsimp [x₀]
        by_cases hS : S = S₀
        · rw [hS, if_pos rfl]
          have htc : typeCounts s₁ S₀ = 1 := by decide
          have hcard : S₀.card = 1 := by decide
          simp [htc, hcard]
        · rw [if_neg hS, Finset.sum_const_zero]
          exact Nat.cast_nonneg _
      · intro i
        dsimp [x₀]
        have hsub : (Finset.univ.filter fun S : Ty 1 => i ∈ S) ⊆ {S₀} := by
          intro S hS
          have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
          rw [Finset.mem_singleton]
          ext j
          fin_cases i; fin_cases j; simpa [S₀] using hiS
        calc
          ∑ S ∈ (Finset.univ.filter fun S : Ty 1 => i ∈ S), (if S = S₀ then (1 : ℝ) else 0)
            ≤ ∑ S ∈ ({S₀} : Finset (Ty 1)), (if S = S₀ then (1 : ℝ) else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => by split_ifs <;> norm_num
          _ = 1 := by simp
      · dsimp [x₀]
        have hmem : S₀ ∈ (Finset.univ : Finset (Ty 1)) := Finset.mem_univ _
        rw [← Finset.add_sum_erase _ _ hmem]
        have herase : ∑ S ∈ (Finset.univ : Finset (Ty 1)).erase S₀,
            ∑ _ ∈ S, (if S = S₀ then (1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero fun S hS =>
            Finset.sum_eq_zero fun _ _ => if_neg (Finset.mem_erase.mp hS).1
        have hcard : S₀.card = 1 := by decide
        rw [herase, add_zero, if_pos rfl]
        simp [hcard]
    have hvol1 : 0 < volume (orderedTimes 1) := by
      have heq : orderedTimes 1 = Set.univ.pi fun _ : Fin 1 => Set.Icc (0 : ℝ) 1 := by
        ext t
        simp only [orderedTimes, mem_ofPred_eq, mem_univ_pi]
        refine ⟨fun h => h.2, fun h => ⟨fun a b hab => by fin_cases a; fin_cases b; exact (lt_irrefl _ hab).elim, h⟩⟩
      rw [heq]
      change 0 < Measure.pi (fun _ : Fin 1 => (volume : Measure ℝ)) _
      rw [Measure.pi_pi]
      simp [Real.volume_Icc]
    have hterm_pos : 0 < (∏ k, (lam (s₁ k) : ℝ≥0∞)) *
        ∫⁻ _ in orderedTimes 1, ENNReal.ofReal (optPois (typeCounts s₁)) := by
      have hp1 : (∏ k, (lam (s₁ k) : ℝ≥0∞)) = 1 := by simp [s₁, lam]
      rw [hp1, one_mul]
      calc
        (0 : ℝ≥0∞) < ∫⁻ _ in orderedTimes 1, (1 : ℝ≥0∞) := by
          simp [lintegral_const, Measure.restrict_apply, hvol1]
        _ ≤ ∫⁻ _ in orderedTimes 1, ENNReal.ofReal (optPois (typeCounts s₁)) :=
          setLIntegral_mono' (measurableSet_orderedTimes 1) fun _ _ =>
            by simpa using ENNReal.ofReal_le_ofReal hopt1
    have hle_sum : (∏ k, (lam (s₁ k) : ℝ≥0∞)) *
        (∫⁻ _ in orderedTimes 1, ENNReal.ofReal (optPois (typeCounts s₁))) ≤
        ∑ s : Fin 1 → Ty 1, (∏ k, (lam (s k) : ℝ≥0∞)) *
          ∫⁻ _ in orderedTimes 1, ENNReal.ofReal (optPois (typeCounts s)) :=
      Finset.single_le_sum
        (f := fun s : Fin 1 → Ty 1 => (∏ k, (lam (s k) : ℝ≥0∞)) *
          ∫⁻ _ in orderedTimes 1, ENNReal.ofReal (optPois (typeCounts s)))
        (fun _ _ => bot_le) (Finset.mem_univ s₁)
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      (lt_of_lt_of_le hterm_pos hle_sum).ne'
  exact ENNReal.toReal_pos hpos.ne' (lt_of_le_of_lt hfin ENNReal.one_lt_top).ne

lemma cStar_le_CR : cStar ≤ CR := by
  unfold CR
  obtain ⟨m₀, lam₀, hpos₀⟩ := exists_pos_optPoisModel
  refine le_csInf ⟨_, m₀, lam₀, hpos₀, rfl⟩ ?_
  rintro r ⟨m, lam, hopt_pos, rfl⟩
  obtain ⟨π₀, hπ₀⟩ := corollary_4_6 m lam
  have hdiv : cStar ≤ algPois lam π₀ / optPoisModel lam :=
    (le_div_iff₀ hopt_pos).mpr hπ₀
  refine hdiv.trans (le_csSup ?_ ⟨π₀, rfl⟩)
  refine ⟨(m : ℝ) / optPoisModel lam, ?_⟩
  rintro q ⟨π, rfl⟩
  exact div_le_div_of_nonneg_right (algPois_le_m lam π) (le_of_lt hopt_pos)

end AuxThm11

open scoped NNReal BigOperators
open OptStochMatch.Tight AuxThm11

theorem solution :
    CR = cStar ∧ CRiid = cStar ∧
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), PolyTimeBits f ∧
      (∀ (m : ℕ) (lam : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), IsListing lam L →
        cStar * optPoisModel lam ≤ algRoutePois lam (machineRule f p L)) ∧
      (∀ (m n : ℕ) (mu : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), 1 ≤ n → ∑ S, mu S = 1 →
        IsListing (iidRates n mu) L →
        cStar * optIID n mu ≤ algRouteIID n mu (machineRule f p L)) :=
  ⟨le_antisymm upper_bound_cgpv.1 cStar_le_CR, theorem_5_5.2, theorem_6_5⟩
