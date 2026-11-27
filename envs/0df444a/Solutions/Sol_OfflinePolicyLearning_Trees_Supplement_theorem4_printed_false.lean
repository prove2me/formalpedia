-- Prove2me | solution 1 for OfflinePolicyLearning.Trees.Supplement.theorem4_printed_false
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:26.536668+00:00
-- url     : https://prove2.me/submissions/86ea5191-f514-442d-9cec-e88e4e66a27b

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_OfflinePolicyLearning_Trees_Supplement_Setting

open MeasureTheory Filter Topology
open OfflinePolicyLearning.Regret

open OfflinePolicyLearning
open OfflinePolicyLearning.Trees
open OfflinePolicyLearning.Trees.Supplement

/-- Theorem 4, p. 28, as printed — under Assumptions 1, 2, 3, the CAIPWL policy over the
depth-`L` tree class on a bounded domain `X ⊂ ℝ^p` satisfies
`R(π̂) = O_p((√((2^L − 1) log p + 2^L log d) + (4/3) L^{1/4} √(2^L − 1)) √(V*/n))`, and in
particular `R(π̂) = O_p(√(V*/n))` — is false for every depth `L ≥ 1` and dimension `p ≥ 1`
(with `d = 2` actions): one instance violates both displayed conclusions. `O_p` is negated in its
weaker per-`n` form. The negated claim adds measurable estimators, a bound on `|μ̂|` and a
positive lower bound on `ê` at each sample size, and evenly sized folds. -/
theorem solution (p L : ℕ) (hp : 1 ≤ p) (hL : 1 ≤ L) :
    ¬ ∀ (S : Set (Fin p → ℝ)) (M : Model S 2) (K : ℕ) (C : CrossFit S 2 K),
        Bornology.IsBounded S →
        (∃ η : ℝ, 0 < η ∧ ∀ x a, η ≤ M.e x a) →
        (∃ B : ℝ, ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) →
        1 < K →
        (∀ (n : ℕ) (k : Fin K),
          n / K ≤ (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ∧
          (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ≤ n / K + 1) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin 2),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs S 2) × S =>
            C.μhat n k q.1 q.2 a) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin 2),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs S 2) × S =>
            C.ehat n k q.1 q.2 a) →
        (∀ n : ℕ, ∃ b : ℝ, ∀ k T x a, |C.μhat n k T x a| ≤ b) →
        (∀ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ k T x a, c ≤ C.ehat n k T x a) →
        (∀ (k : Fin K) (a : Fin 2),
          Tendsto (fun n : ℕ => (n : ℝ) * (C.mseMu M n k a * C.mseE M n k a)) atTop (𝓝 0)) →
        (∃ Cc Dc ω : ℝ, 0 < Cc ∧ 0 < Dc ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            hammingCoverNum ε (treePoliciesOn p 2 L S) ≠ ⊤ ∧
            ((hammingCoverNum ε (treePoliciesOn p 2 L S)).toNat : ℝ) ≤
              Cc * Real.exp (Dc * (1 / ε) ^ ω)) →
        ∀ πh : (n : ℕ) → (Fin n → Draw S 2) → S → Fin 2,
          (∀ n D, πh n D ∈ treePoliciesOn p 2 L S) →
          (∀ n D, ∀ π ∈ treePoliciesOn p 2 L S, C.Qhat D π ≤ C.Qhat D (πh n D)) →
          (∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
            M.sample n {D | Mc < |M.regret (treePoliciesOn p 2 L S) (πh n D) /
              ((Real.sqrt ((2 ^ L - 1 : ℝ) * Real.log p + (2 : ℝ) ^ L * Real.log 2) +
                  4 / 3 * (L : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ L - 1 : ℝ)) *
                Real.sqrt (M.Vstar (treePoliciesOn p 2 L S) / n))|} ≤ ENNReal.ofReal ε) ∨
          (∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
            M.sample n {D | Mc < |M.regret (treePoliciesOn p 2 L S) (πh n D) /
                Real.sqrt (M.Vstar (treePoliciesOn p 2 L S) / n)|} ≤ ENNReal.ofReal ε) := by
                  classical
                  -- constant trees
                  have htree : ∀ (a : Fin 2), ∃ T : DTree p 2 L, ∀ x, T.eval x = a := by
                    intro a
                    induction L, hL using Nat.le_induction with
                    | base => exact ⟨DTree.leaf a, fun x => rfl⟩
                    | succ m hm ih =>
                      obtain ⟨T, hT⟩ := ih
                      refine ⟨DTree.node ⟨0, hp⟩ 0 T T, fun x => ?_⟩
                      simp [DTree.eval, hT]
                  intro H
                  obtain ⟨S, hS⟩ : ∃ S : Set (Fin p → ℝ), S = {0} := ⟨_, rfl⟩
                  have hsub : Subsingleton S := by
                    subst hS; infer_instance
                  obtain ⟨x0⟩ : Nonempty S := by
                    subst hS; exact ⟨⟨0, rfl⟩⟩
                  have hpol : treePoliciesOn p 2 L S = Set.univ := by
                    ext π
                    simp only [treePoliciesOn, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
                    obtain ⟨T, hT⟩ := htree (π x0)
                    exact ⟨T, fun x => by rw [hT, Subsingleton.elim x x0]⟩
                  obtain ⟨ν, hνP, hν⟩ : ∃ ν : Measure (Fin 2), IsProbabilityMeasure ν ∧ ∀ a, ν {a} = 2⁻¹ := by
                    refine ⟨(2⁻¹ : ENNReal) • Measure.count, ⟨?_⟩, fun a => ?_⟩
                    · simp [ENNReal.inv_mul_cancel]
                    · simp
                  obtain ⟨y0, hy0⟩ : ∃ y0 : Fin 2 → ℝ, y0 = fun a => if a = 0 then 1 else 0 := ⟨_, rfl⟩
                  let M : Model S 2 :=
                    { PX := Measure.dirac x0
                      κY := ProbabilityTheory.Kernel.const _ (Measure.dirac y0)
                      κA := ProbabilityTheory.Kernel.const _ ν }
                  let C : CrossFit S 2 2 :=
                    { fold := fun n i => ⟨(i : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩
                      μhat := fun n _ _ _ _ => (n : ℝ) + 1
                      ehat := fun _ _ _ _ _ => 1 / 2 }
                  have hMe : ∀ x a, M.e x a = 1 / 2 := by
                    intro x a
                    simp [Model.e, M, hν]
                  have hMμ : ∀ x a, M.μ x a = y0 a := by
                    intro x a
                    simp [Model.μ, M]
                  have hlaw : M.law = (Measure.dirac x0).prod ((Measure.dirac y0).prod ν) := by
                    simp [Model.law, M, ProbabilityTheory.Kernel.prod_const, Measure.compProd_const]
                  have hlawP : IsProbabilityMeasure M.law := by rw [hlaw]; infer_instance
                  have hae : ∀ᵐ ω ∂M.law, ω.2.1 = y0 := by
                    have h1 : MeasurePreserving (fun ω : Draw S 2 => ω.2.1) M.law (Measure.dirac y0) := by
                      rw [hlaw]
                      exact (measurePreserving_fst (μ := Measure.dirac y0) (ν := ν)).comp
                        (measurePreserving_snd (μ := Measure.dirac x0) (ν := (Measure.dirac y0).prod ν))
                    have h2 : ∀ᵐ y ∂(Measure.dirac y0), y = y0 := by
                      rw [ae_dirac_eq]; simp
                    exact h1.quasiMeasurePreserving.ae h2
                  -- value
                  have hQ : ∀ π : S → Fin 2, M.Q π = y0 (π x0) := by
                    intro π
                    have : M.Q π = ∫ ω, y0 (π x0) ∂M.law := by
                      refine integral_congr_ae ?_
                      filter_upwards [hae] with ω hω
                      rw [hω, Subsingleton.elim ω.1 x0]
                    rw [this]; simp
                  have hfin : Finite (Set.univ : Set (S → Fin 2)) := Set.finite_univ
                  have hreg : 1 ≤ M.regret Set.univ (fun _ => (1 : Fin 2)) := by
                    have h1 : M.Q (fun _ => (0 : Fin 2)) ≤ ⨆ π' : (Set.univ : Set (S → Fin 2)), M.Q π'.1 :=
                      le_ciSup (f := fun π' : (Set.univ : Set (S → Fin 2)) => M.Q π'.1)
                        (Set.finite_range _).bddAbove ⟨_, Set.mem_univ _⟩
                    rw [hQ] at h1
                    unfold Model.regret
                    rw [hQ]
                    simp only [hy0] at h1 ⊢
                    simp at h1 ⊢
                    linarith
                  have hV : 1 ≤ M.Vstar Set.univ := by
                    let π0 : (Set.univ : Set (S → Fin 2)) := ⟨fun _ => 0, Set.mem_univ _⟩
                    let π1 : (Set.univ : Set (S → Fin 2)) := ⟨fun _ => 1, Set.mem_univ _⟩
                    have hval : ∫ ω, (M.Γ (obs ω) (π0.1 ω.1) - M.Γ (obs ω) (π1.1 ω.1)) ^ 2 ∂M.law = 1 := by
                      have : ∫ ω, (M.Γ (obs ω) (π0.1 ω.1) - M.Γ (obs ω) (π1.1 ω.1)) ^ 2 ∂M.law
                          = ∫ ω, (1 : ℝ) ∂M.law := by
                        refine integral_congr_ae ?_
                        filter_upwards [hae] with ω hω
                        simp [Model.Γ, obs, hMμ, hω, π0, π1, hy0]
                      rw [this]; simp
                    have h1 : ∀ πa : (Set.univ : Set (S → Fin 2)),
                        ∫ ω, (M.Γ (obs ω) (πa.1 ω.1) - M.Γ (obs ω) (π1.1 ω.1)) ^ 2 ∂M.law ≤
                        ⨆ πb : (Set.univ : Set (S → Fin 2)),
                          ∫ ω, (M.Γ (obs ω) (πa.1 ω.1) - M.Γ (obs ω) (πb.1 ω.1)) ^ 2 ∂M.law := fun πa =>
                      le_ciSup (f := fun πb : (Set.univ : Set (S → Fin 2)) =>
                          ∫ ω, (M.Γ (obs ω) (πa.1 ω.1) - M.Γ (obs ω) (πb.1 ω.1)) ^ 2 ∂M.law)
                        (Set.finite_range _).bddAbove π1
                    have h2 : (⨆ πb : (Set.univ : Set (S → Fin 2)),
                          ∫ ω, (M.Γ (obs ω) (π0.1 ω.1) - M.Γ (obs ω) (πb.1 ω.1)) ^ 2 ∂M.law) ≤
                        M.Vstar Set.univ :=
                      le_ciSup (f := fun πa : (Set.univ : Set (S → Fin 2)) =>
                        ⨆ πb : (Set.univ : Set (S → Fin 2)),
                          ∫ ω, (M.Γ (obs ω) (πa.1 ω.1) - M.Γ (obs ω) (πb.1 ω.1)) ^ 2 ∂M.law)
                        (Set.finite_range _).bddAbove π0
                    calc (1 : ℝ) = _ := hval.symm
                      _ ≤ _ := h1 π0
                      _ ≤ _ := h2
                  -- learned policy
                  have hmax : ∀ (n : ℕ) (D : Fin n → Draw S 2), ∃ π : S → Fin 2, ∀ π', C.Qhat D π' ≤ C.Qhat D π :=
                    fun n D => Finite.exists_max (fun π => C.Qhat D π)
                  choose πh hπh using hmax
                  -- sign sum event
                  let sg : Fin 2 → ℤ := fun a => if a = 0 then 1 else -1
                  have hsg : ∀ a, sg a.rev = - sg a := by
                    intro a; fin_cases a <;> simp [sg]
                  have hsgodd : ∀ a, ∃ t : ℤ, sg a = 2 * t + 1 := by
                    intro a; fin_cases a
                    · exact ⟨0, by simp [sg]⟩
                    · exact ⟨-1, by simp [sg]⟩
                  have hhalf : ∀ n : ℕ, Odd n → 1 ≤ 2 * M.sample n {D | 0 < ∑ i, sg (D i).2.2} := by
                    intro n hn
                    let φ : Draw S 2 → Draw S 2 := fun ω => (ω.1, (ω.2.1, ω.2.2.rev))
                    have hrev : MeasurePreserving (Fin.rev : Fin 2 → Fin 2) ν ν := by
                      refine ⟨measurable_of_countable _, ?_⟩
                      refine Measure.ext_of_singleton fun a => ?_
                      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a), hν]
                      have : (Fin.rev : Fin 2 → Fin 2) ⁻¹' {a} = {a.rev} := by
                        ext b; simp [Fin.rev_eq_iff]
                      rw [this, hν]
                    have hφ : MeasurePreserving φ M.law M.law := by
                      rw [hlaw]
                      exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hrev)
                    have hΦ : MeasurePreserving (fun (D : Fin n → Draw S 2) i => φ (D i)) (M.sample n)
                        (M.sample n) :=
                      measurePreserving_pi (fun _ => M.law) (fun _ => M.law) (fun _ => hφ)
                    have hmeas : MeasurableSet {D : Fin n → Draw S 2 | 0 < ∑ i, sg (D i).2.2} := by
                      have h1 : Measurable (fun (D : Fin n → Draw S 2) i => (D i).2.2) := by
                        fun_prop
                      exact h1 (MeasurableSet.of_discrete (s := {a : Fin n → Fin 2 | 0 < ∑ i, sg (a i)}))
                    have hpre := hΦ.measure_preimage hmeas.nullMeasurableSet
                    have hne : ∀ a : Fin n → Fin 2, ∑ i, sg (a i) ≠ 0 := by
                      intro a h0
                      choose t ht using hsgodd
                      obtain ⟨m, hm⟩ := hn
                      have : ∑ i, sg (a i) = 2 * ∑ i, t (a i) + n := by
                        simp only [ht, Finset.sum_add_distrib, Finset.mul_sum]
                        simp
                      omega
                    have hcover : (Set.univ : Set (Fin n → Draw S 2)) ⊆ {D | 0 < ∑ i, sg (D i).2.2} ∪
                        ((fun (D : Fin n → Draw S 2) i => φ (D i)) ⁻¹' {D | 0 < ∑ i, sg (D i).2.2}) := by
                      intro D _
                      have := hne (fun i => (D i).2.2)
                      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, φ, hsg,
                        Finset.sum_neg_distrib]
                      omega
                    have hP : IsProbabilityMeasure (M.sample n) := by
                      unfold Model.sample; infer_instance
                    calc (1 : ENNReal) = M.sample n Set.univ := measure_univ.symm
                      _ ≤ _ := measure_mono hcover
                      _ ≤ _ := measure_union_le _ _
                      _ = _ := by rw [hpre, two_mul]
                  have haeD : ∀ n : ℕ, ∀ᵐ D ∂M.sample n, ∀ i, (D i).2.1 = y0 := by
                    intro n
                    rw [ae_all_iff]
                    intro i
                    exact (measurePreserving_eval (fun _ : Fin n => M.law) i).quasiMeasurePreserving.ae hae
                  have hwrong : ∀ (n : ℕ) (D : Fin n → Draw S 2), 0 < n → (∀ i, (D i).2.1 = y0) →
                      0 < ∑ i, sg (D i).2.2 → πh n D = fun _ => 1 := by
                    intro n D hn hD hpos
                    have hterm : ∀ i, C.GammaHat D i 1 - C.GammaHat D i 0 =
                        2 * (n + 1) * (sg (D i).2.2 : ℝ) - 2 * (if (D i).2.2 = 0 then 1 else 0) := by
                      intro i
                      have h2 := hD i
                      simp only [CrossFit.GammaHat, CrossFit.μhatAt, CrossFit.ehatAt, obs, C, h2, sg]
                      rcases (show (D i).2.2 = 0 ∨ (D i).2.2 = 1 by omega) with h | h
                      · simp [h, hy0]; ring
                      · simp [h, hy0]; ring
                    have hlt : C.Qhat D (fun _ => 0) < C.Qhat D (fun _ => 1) := by
                      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
                      unfold CrossFit.Qhat
                      refine mul_lt_mul_of_pos_left ?_ (by positivity)
                      rw [← sub_pos, ← Finset.sum_sub_distrib]
                      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, ← Finset.mul_sum,
                        ← Finset.mul_sum]
                      have h1 : (1 : ℝ) ≤ ∑ i, (sg (D i).2.2 : ℝ) := by
                        have : (1 : ℤ) ≤ ∑ i, sg (D i).2.2 := hpos
                        exact_mod_cast this
                      have h2 : ∑ i : Fin n, (if (D i).2.2 = 0 then (1 : ℝ) else 0) ≤ n := by
                        calc _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
                          _ = n := by simp
                      nlinarith
                    funext x
                    have h0 : πh n D x ≠ 0 := by
                      intro h0
                      have : πh n D = fun _ => 0 := by
                        funext x'; rw [Subsingleton.elim x' x, h0]
                      have h3 := hπh n D (fun _ => 1)
                      rw [this] at h3
                      exact absurd h3 (not_le.mpr hlt)
                    omega
                  -- negation of both
                  have key : ∀ c : ℝ, 0 < c → ¬ (∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
                            M.sample n {D | Mc < |M.regret (treePoliciesOn p 2 L S) (πh n D) /
                              (c * Real.sqrt (M.Vstar (treePoliciesOn p 2 L S) / n))|} ≤ ENNReal.ofReal ε) := by
                    intro c hc h
                    obtain ⟨Mc, hMc, N, hN⟩ := h (1 / 4) (by norm_num)
                    rw [hpol] at hN
                    obtain ⟨m, hm⟩ := exists_nat_gt ((Mc * c) ^ 2 * M.Vstar Set.univ)
                    let n := 2 * (max N m) + 1
                    have hnN : n ≥ N := by have := le_max_left N m; omega
                    have hnm : m ≤ n := by have := le_max_right N m; omega
                    have hnpos : 0 < n := by omega
                    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
                    have hV0 : 0 < M.Vstar Set.univ := by linarith
                    have hle : M.sample n {D | 0 < ∑ i, sg (D i).2.2} ≤ ENNReal.ofReal (1 / 4) := by
                      refine le_trans (measure_mono_ae ?_) (hN n hnN)
                      filter_upwards [haeD n] with D hD hDpos
                      have hw := hwrong n D hnpos hD hDpos
                      show Mc < _
                      rw [hw]
                      have hr : 0 < c * Real.sqrt (M.Vstar Set.univ / n) := by positivity
                      have h1 : Mc * (c * Real.sqrt (M.Vstar Set.univ / n)) < 1 := by
                        have h2 : (Mc * c * Real.sqrt (M.Vstar Set.univ / n)) ^ 2 < 1 := by
                          rw [mul_pow, Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hnR]
                          have : (m : ℝ) ≤ n := by exact_mod_cast hnm
                          linarith
                        have h3 : 0 ≤ Mc * c * Real.sqrt (M.Vstar Set.univ / n) := by positivity
                        rw [← mul_assoc]
                        nlinarith
                      refine lt_of_lt_of_le ?_ (le_abs_self _)
                      rw [lt_div_iff₀ hr]
                      linarith
                    have h2 := hhalf n ⟨max N m, rfl⟩
                    have h3 : (1 : ENNReal) ≤ 2 * ENNReal.ofReal (1 / 4) := le_trans h2 (by gcongr)
                    have h4 : (2 : ENNReal) * ENNReal.ofReal (1 / 4) = ENNReal.ofReal (1 / 2) := by
                      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
                      norm_num
                    rw [h4, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h3
                    norm_num at h3
                  have hcard : ∀ (n : ℕ) (k : Fin 2),
                      (Finset.univ.filter fun i : Fin n => C.fold n i = k).card = (n + 1 - k) / 2 := by
                    intro n k
                    have h1 : (Finset.univ.filter fun i : Fin n => C.fold n i = k).card
                        = ∑ i : Fin n, if (i : ℕ) % 2 = (k : ℕ) then 1 else 0 := by
                      rw [Finset.card_filter]
                      refine Finset.sum_congr rfl fun i _ => ?_
                      simp [C, Fin.ext_iff]
                    rw [h1, Fin.sum_univ_eq_sum_range (fun i => if i % 2 = (k : ℕ) then 1 else 0) n]
                    clear h1
                    have hk := k.2
                    induction n with
                    | zero => simp; omega
                    | succ n ih =>
                      rw [Finset.sum_range_succ, ih]
                      split_ifs <;> omega
                  refine Or.elim (H S M 2 C ?_ ⟨1 / 2, by norm_num, fun x a => (hMe x a).ge⟩ ?_ (by norm_num) ?_ ?_ ?_ ?_ ?_
                    ?_ ?_ πh ?_ ?_) (fun h => ?_) (fun h => ?_)
                  rotate_right 2
                  · refine key _ ?_ h
                    have h1 : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
                    have h2 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
                    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
                    have h4 : 0 ≤ (2 ^ L - 1 : ℝ) := by linarith
                    have h5 : 0 < (2 ^ L - 1 : ℝ) * Real.log p + (2 : ℝ) ^ L * Real.log 2 := by positivity
                    have h6 := Real.sqrt_pos.mpr h5
                    positivity
                  · exact key 1 one_pos (by simpa only [one_mul] using h)
                  · exact hS ▸ Bornology.isBounded_singleton
                  · refine ⟨1, fun x => ?_⟩
                    have : ∀ᵐ y ∂(Measure.dirac y0), ∀ a, |y a| ≤ 1 := by
                      rw [ae_dirac_iff]
                      · intro a; rw [hy0]; dsimp only; split_ifs <;> simp
                      · rw [Set.ofPred_forall]
                        exact MeasurableSet.iInter (f := fun a => {y : Fin 2 → ℝ | |y a| ≤ 1}) fun a =>
                          measurableSet_le (by fun_prop) measurable_const
                    simpa [M] using this
                  · intro n k
                    rw [hcard]
                    have := k.2
                    omega
                  · intro n k a; exact measurable_const
                  · intro n k a; exact measurable_const
                  · intro n; exact ⟨|(n : ℝ) + 1|, fun _ _ _ _ => le_rfl⟩
                  · intro n; exact ⟨1 / 2, by norm_num, fun _ _ _ _ => le_rfl⟩
                  · intro k a
                    have : ∀ n, C.mseE M n k a = 0 := by
                      intro n
                      simp [CrossFit.mseE, hMe, C]
                    simp [this]
                  · refine ⟨2, 1, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num, fun ε hε _ => ?_⟩
                    have hN : hammingCoverNum ε (treePoliciesOn p 2 L S) ≤ 2 := by
                      rw [hpol]
                      unfold hammingCoverNum
                      refine iSup_le fun m => iSup_le fun hm => iSup_le fun x => ?_
                      have : hammingCoverNumOn ε (Set.univ : Set (S → Fin 2)) x ≤ 2 := by
                        refine Nat.sInf_le ⟨fun i _ => i, fun i => Set.mem_univ _, fun π _ => ⟨π x0, ?_⟩⟩
                        have : ∀ j, π (x j) = π x0 := fun j => by rw [Subsingleton.elim (x j) x0]
                        simp [OfflinePolicyLearning.Regret.hammingDist, this, hε.le]
                      exact_mod_cast this
                    refine ⟨ne_top_of_le_ne_top (by simp) hN, ?_⟩
                    have h1 : (hammingCoverNum ε (treePoliciesOn p 2 L S)).toNat ≤ 2 :=
                      ENat.toNat_le_of_le_natCast hN
                    have h2 : (1 : ℝ) ≤ Real.exp (1 * (1 / ε) ^ (1 / 4 : ℝ)) := Real.one_le_exp (by positivity)
                    have h3 : ((hammingCoverNum ε (treePoliciesOn p 2 L S)).toNat : ℝ) ≤ 2 := by exact_mod_cast h1
                    linarith
                  · intro n D; rw [hpol]; trivial
                  · intro n D π _; exact hπh n D π
