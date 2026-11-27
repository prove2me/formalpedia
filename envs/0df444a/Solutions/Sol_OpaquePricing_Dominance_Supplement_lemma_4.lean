-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:39.744917+00:00
-- url     : https://prove2.me/submissions/70fdc0be-4aef-43fd-8321-9a9a82194b94

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) 0 ≤
      ENNReal.ofReal (4 - 2 / (N : ℝ)) * optSP (Measure.pi (fun _ : Fin N => ν)) := by
        set_option maxHeartbeats 4000000 in
          set_option maxRecDepth 2000 in
            set_option backward.isDefEq.respectTransparency false in
              classical
              have oneD : ∀ (M : ℕ) (C D : ℝ), 0 ≤ C → 0 ≤ D →
                  (∀ (t : ℝ) (s : Set ℝ), 0 ≤ t → MeasurableSet s → s ⊆ Set.Ici t →
                    ENNReal.ofReal t * ν s ≤ ENNReal.ofReal C + ENNReal.ofReal D * ν s) →
                  ∀ (a : ℝ → ℕ) (u : ℝ → ℝ), Measurable a →
                  (∀ x, a x ≤ M) → (∀ x, 0 ≤ x → 0 ≤ u x) →
                  (∀ x y, 0 ≤ x → 0 ≤ y → u y + (x-y) * (a y : ℝ) ≤ u x) →
                  (∫⁻ x, ENNReal.ofReal (x * (a x : ℝ) - u x) ∂ν) ≤
                    (M : ENNReal) * ENNReal.ofReal C +
                      ENNReal.ofReal D * ∫⁻ x, (a x : ENNReal) ∂ν := by
                intro M C D hC hD hd a u ha hM hu hic
                let S : ℕ → Set ℝ := fun j => {x | 0 ≤ x ∧ j ≤ a x}
                let t : ℕ → ℝ := fun j => if h : (S j).Nonempty then sInf (S j) else 0
                have hSm : ∀ j, MeasurableSet (S j) := fun j =>
                  (measurableSet_le measurable_const measurable_id).inter
                    (measurableSet_le measurable_const ha)
                have ht0 : ∀ j, 0 ≤ t j := by
                  intro j
                  dsimp [t]
                  split_ifs with h
                  · exact le_csInf h (fun x hx => hx.1)
                  · rfl
                have htx : ∀ j x, x ∈ S j → t j ≤ x := by
                  intro j x hx
                  dsimp [t]
                  rw [if_pos (show (S j).Nonempty from ⟨x, hx⟩)]
                  exact csInf_le ⟨0, fun z hz => hz.1⟩ hx
                have hclaim : ∀ j x, 0 ≤ x → j ≤ a x →
                    (j : ℝ) * x - ∑ l ∈ Finset.range j, t (l+1) ≤ u x := by
                  intro j
                  induction j with
                  | zero => intro x hx hj; simpa using hu x hx
                  | succ j ih =>
                    intro x hx hj
                    have hne : (S (j+1)).Nonempty := ⟨x, hx, hj⟩
                    have hl : ((j+1 : ℕ) : ℝ) * x -
                        (∑ l ∈ Finset.range j, t (l+1)) - u x ≤ t (j+1) := by
                      rw [show t (j+1) = sInf (S (j+1)) by simp [t, hne]]
                      apply le_csInf hne
                      intro y hy
                      have hjx := ih x hx (by omega)
                      have hjy := ih y hy.1 (by have := hy.2; omega)
                      by_cases hyx : y ≤ x
                      · have hs := hic x y hx hy.1
                        have hay : ((j+1 : ℕ) : ℝ) ≤ a y := by exact_mod_cast hy.2
                        have hh := mul_le_mul_of_nonneg_left hay (sub_nonneg.mpr hyx)
                        push_cast at hh ⊢
                        nlinarith
                      · push_cast at hjx ⊢
                        linarith
                    rw [Finset.sum_range_succ]
                    push_cast at hl ⊢
                    linarith
                have hcount : ∀ x, ∑ j ∈ Finset.range M,
                    (S (j+1)).indicator (1 : ℝ → ENNReal) x ≤ (a x : ENNReal) := by
                  intro x
                  by_cases hx : 0 ≤ x
                  · have heq : ∑ j ∈ Finset.range M,
                        (S (j+1)).indicator (1 : ℝ → ENNReal) x =
                          ∑ j ∈ Finset.range (a x), (1 : ENNReal) := by
                      calc
                        _ = ∑ j ∈ Finset.range (a x),
                            (S (j+1)).indicator (1 : ℝ → ENNReal) x := by
                          symm
                          apply Finset.sum_subset (Finset.range_mono (hM x))
                          intro j hj hj'
                          have hjn : a x ≤ j := by simpa using hj'
                          apply Set.indicator_of_notMem
                          simp only [S, Set.mem_setOf_eq, not_and]
                          intro _; omega
                        _ = _ := by
                          apply Finset.sum_congr rfl
                          intro j hj
                          apply Set.indicator_of_mem
                          exact ⟨hx, by have := Finset.mem_range.mp hj; omega⟩
                    simpa using heq.le
                  · simp [S, hx]
                have hpw : ∀ᵐ x ∂ν, ENNReal.ofReal (x * (a x : ℝ) - u x) ≤
                    ∑ j ∈ Finset.range M, ENNReal.ofReal (t (j+1)) *
                      (S (j+1)).indicator (1 : ℝ → ENNReal) x := by
                  filter_upwards [hν] with x hx
                  have hc := hclaim (a x) x hx le_rfl
                  have heq : (∑ j ∈ Finset.range M,
                        (S (j+1)).indicator (fun _ => t (j+1)) x) =
                      ∑ j ∈ Finset.range (a x), t (j+1) := by
                    calc
                      _ = ∑ j ∈ Finset.range (a x),
                          (S (j+1)).indicator (fun _ => t (j+1)) x := by
                        symm
                        apply Finset.sum_subset (Finset.range_mono (hM x))
                        intro j hj hj'
                        apply Set.indicator_of_notMem
                        simp only [S, Set.mem_setOf_eq, not_and]
                        intro _
                        have : a x ≤ j := by simpa using hj'
                        omega
                      _ = _ := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        apply Set.indicator_of_mem
                        exact ⟨hx, by have := Finset.mem_range.mp hj; omega⟩
                  calc
                    _ ≤ ENNReal.ofReal (∑ j ∈ Finset.range M,
                        (S (j+1)).indicator (fun _ => t (j+1)) x) := by
                      apply ENNReal.ofReal_le_ofReal
                      rw [heq]
                      linarith
                    _ = _ := by
                      rw [ENNReal.ofReal_sum_of_nonneg]
                      · apply Finset.sum_congr rfl
                        intro j hj
                        by_cases hxj : x ∈ S (j+1)
                        · simp [Set.indicator_of_mem hxj]
                        · simp [Set.indicator_of_notMem hxj]
                      · intro j hj
                        exact Set.indicator_nonneg (fun _ _ => ht0 _) _
                calc
                  _ ≤ ∫⁻ x, ∑ j ∈ Finset.range M, ENNReal.ofReal (t (j+1)) *
                      (S (j+1)).indicator (1 : ℝ → ENNReal) x ∂ν := lintegral_mono_ae hpw
                  _ = ∑ j ∈ Finset.range M, ENNReal.ofReal (t (j+1)) * ν (S (j+1)) := by
                    rw [lintegral_finsetSum]
                    · apply Finset.sum_congr rfl
                      intro j hj
                      rw [lintegral_const_mul _ (measurable_one.indicator (hSm _)),
                        lintegral_indicator_one (hSm _)]
                    · intro j hj
                      exact (measurable_const.indicator (hSm _)).const_mul _
                  _ ≤ ∑ j ∈ Finset.range M,
                      (ENNReal.ofReal C + ENNReal.ofReal D * ν (S (j+1))) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    exact hd _ _ (ht0 _) (hSm _) (fun x hx => htx _ _ hx)
                  _ = (M : ENNReal) * ENNReal.ofReal C + ENNReal.ofReal D *
                      ∑ j ∈ Finset.range M, ν (S (j+1)) := by
                    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                      nsmul_eq_mul, Finset.mul_sum]
                  _ ≤ _ := by
                    gcongr
                    calc
                      _ = ∫⁻ x, ∑ j ∈ Finset.range M,
                          (S (j+1)).indicator (1 : ℝ → ENNReal) x ∂ν := by
                        rw [lintegral_finsetSum]
                        · apply Finset.sum_congr rfl
                          intro j hj
                          rw [lintegral_indicator_one (hSm _)]
                        · intro j hj
                          exact measurable_const.indicator (hSm _)
                      _ ≤ _ := lintegral_mono hcount
              obtain ⟨n, rfl⟩ : ∃ n, N = n+1 := ⟨N-1, by omega⟩
              let μ := Measure.pi (fun _ : Fin (n+1) => ν)
              have hnp : (0 : ℝ) < n+1 := by positivity
              have hn0 : (0 : ENNReal) < n+1 := by positivity
              have hc : (0 : ℝ) < 4 - 2 / ((n+1 : ℕ) : ℝ) := by
                have hh : (2 : ℝ) ≤ n+1 := by exact_mod_cast hN
                have hh' : 2 / (n+1 : ℝ) ≤ 1 := (div_le_one hnp).2 hh
                push_cast
                linarith
              by_cases htop : optSP μ = ⊤
              · change optOPQ μ 0 ≤ _
                rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
                exact le_top
              let R : ℝ := (optSP μ).toReal
              have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
              have hR : ENNReal.ofReal R = optSP μ := ENNReal.ofReal_toReal htop
              have hSP : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} ≤ ENNReal.ofReal R := by
                intro t ht
                rw [hR]
                exact le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => expSP μ t) t ht
              have hunion : ∀ s : Set ℝ, MeasurableSet s →
                  μ.real {v | ∃ i, v i ∈ s} = 1 - (1 - ν.real s)^(n+1) := by
                intro s hs
                have hm : MeasurableSet {v : Fin (n+1) → ℝ | ∃ i, v i ∈ s} := by
                  simp only [Set.ofPred_exists]
                  exact MeasurableSet.iUnion fun i => hs.preimage (measurable_pi_apply i)
                have heq : {v : Fin (n+1) → ℝ | ∃ i, v i ∈ s} =
                    (Set.univ.pi (fun _ : Fin (n+1) => sᶜ))ᶜ := by
                  ext v
                  simp
                rw [heq, measureReal_compl (MeasurableSet.univ_pi fun _ => hs.compl), probReal_univ]
                congr 1
                change (Measure.pi (fun _ : Fin (n+1) => ν) (Set.univ.pi (fun _ => sᶜ))).toReal = _
                rw [Measure.pi_pi]
                simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
                congr 1
                exact measureReal_compl hs |>.trans (by rw [probReal_univ])
              have hbern : ∀ (z : ℝ), 0 ≤ z → z ≤ 1 → ∀ k : ℕ,
                  (1-z)^k * (1 + (k : ℝ)*z) ≤ 1 := by
                intro z hz hz1 k
                induction k with
                | zero => simp
                | succ k ih =>
                  have hp : 0 ≤ (1-z)^k := pow_nonneg (by linarith) _
                  have hh : (1-z)*(1 + ((k+1 : ℕ) : ℝ)*z) ≤ 1 + (k : ℝ)*z := by
                    push_cast
                    nlinarith [sq_nonneg z, mul_nonneg (show (0 : ℝ) ≤ k by positivity) (sq_nonneg z)]
                  calc
                    _ = (1-z)^k * ((1-z)*(1 + ((k+1 : ℕ) : ℝ)*z)) := by rw [pow_succ]; ring
                    _ ≤ (1-z)^k * (1 + (k : ℝ)*z) := mul_le_mul_of_nonneg_left hh hp
                    _ ≤ 1 := ih
              have hdual : ∀ (t : ℝ) (s : Set ℝ), 0 ≤ t → MeasurableSet s → s ⊆ Set.Ici t →
                  ENNReal.ofReal t * ν s ≤ ENNReal.ofReal (R/(n+1 : ℝ)) + ENNReal.ofReal R * ν s := by
                intro t s ht hs hst
                have hm : μ {v | ∃ i, v i ∈ s} ≤ μ {v | ∃ i, t ≤ v i} := by
                  apply measure_mono
                  rintro v ⟨i, hi⟩
                  exact ⟨i, hst hi⟩
                have hr : t * μ.real {v | ∃ i, v i ∈ s} ≤ R := by
                  have hh : ENNReal.ofReal t * μ {v | ∃ i, v i ∈ s} ≤ ENNReal.ofReal R := by
                    calc _ ≤ ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} := by gcongr
                         _ ≤ _ := hSP t ht
                  have := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal R ≠ ⊤) hh
                  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hR0, ← measureReal_def] using this
                rw [hunion s hs] at hr
                have hz0 : 0 ≤ ν.real s := measureReal_nonneg
                have hz1 : ν.real s ≤ 1 := measureReal_le_one
                have hb := hbern (ν.real s) hz0 hz1 (n+1)
                have hh : (n+1 : ℝ) * ν.real s ≤
                    (1 + (n+1 : ℝ)*ν.real s) * (1-(1-ν.real s)^(n+1)) := by
                  push_cast at hb
                  nlinarith
                have hprod := mul_le_mul_of_nonneg_left hh ht
                have hprod' := mul_le_mul_of_nonneg_left hr
                  (show 0 ≤ 1 + (n+1 : ℝ)*ν.real s by positivity)
                have hfin : t * ν.real s ≤ R/(n+1 : ℝ) + R*ν.real s := by
                  have hh2 : (t * ν.real s - R * ν.real s) * (n+1 : ℝ) ≤ R := by nlinarith
                  have hh3 := (le_div_iff₀ hnp).2 hh2
                  linarith
                have hv : ENNReal.ofReal (ν.real s) = ν s := ENNReal.ofReal_toReal (by finiteness)
                rw [← hv, ← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul hR0,
                  ← ENNReal.ofReal_add (by positivity) (by positivity)]
                exact ENNReal.ofReal_le_ofReal hfin
              have hnonneg : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i := by
                apply ae_all_iff.mpr
                intro i
                exact (measurePreserving_eval (fun _ : Fin (n+1) => ν) i).quasiMeasurePreserving.tendsto_ae hν
              have auction : ∀ (M : ℕ) (a : (Fin (n+1) → ℝ) → Fin (n+1) → ℕ)
                  (u : (Fin (n+1) → ℝ) → Fin (n+1) → ℝ),
                  (∀ i, Measurable fun v => a v i) → (∀ i, Measurable fun v => u v i) →
                  (∀ v, ∑ i, a v i ≤ M) →
                  (∀ v i, (∀ j, 0 ≤ v j) → 0 ≤ u v i) →
                  (∀ v i x y, (∀ j, 0 ≤ v j) → 0 ≤ x → 0 ≤ y →
                    u (Function.update v i y) i + (x-y)*(a (Function.update v i y) i : ℝ) ≤
                      u (Function.update v i x) i) →
                  (∫⁻ v, ∑ i, ENNReal.ofReal (v i*(a v i : ℝ) - u v i) ∂μ) ≤
                    (2 : ENNReal) * M * ENNReal.ofReal R := by
                intro M a u ha hu hM hu0 hic
                have hMa : ∀ v i, a v i ≤ M := fun v i =>
                  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (hM v)
                have hcoord : ∀ i, (∫⁻ v, ENNReal.ofReal (v i*(a v i : ℝ) - u v i) ∂μ) ≤
                    (M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ)) +
                      ENNReal.ofReal R * ∫⁻ v, (a v i : ENNReal) ∂μ := by
                  intro i
                  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
                  let ρ := Measure.pi (fun _ : Fin n => ν)
                  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) i
                  have hen := he.symm e
                  have hρ : ∀ᵐ w ∂ρ, ∀ j, 0 ≤ w j := by
                    apply ae_all_iff.mpr
                    intro j
                    exact (measurePreserving_eval (fun _ : Fin n => ν) j).quasiMeasurePreserving.tendsto_ae hν
                  have hfi : Measurable fun v => ENNReal.ofReal (v i*(a v i : ℝ) - u v i) := by
                    exact ((measurable_pi_apply i).mul ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (ha i))).sub (hu i) |>.ennreal_ofReal
                  have hAi : Measurable fun v => (a v i : ENNReal) := (measurable_of_countable (fun k : ℕ => (k : ENNReal))).comp (ha i)
                  rw [← hen.lintegral_comp hfi]
                  change (∫⁻ z, ((fun v => ENNReal.ofReal (v i*(a v i : ℝ) - u v i)) ∘ e.symm) z ∂ν.prod ρ) ≤ _
                  rw [lintegral_prod_symm _ ((hfi.comp e.symm.measurable).aemeasurable)]
                  have hfiber : ∀ᵐ w ∂ρ,
                      (∫⁻ x, ENNReal.ofReal ((e.symm (x,w)) i * (a (e.symm (x,w)) i : ℝ) - u (e.symm (x,w)) i) ∂ν) ≤
                      (M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ)) +
                        ENNReal.ofReal R * ∫⁻ x, (a (e.symm (x,w)) i : ENNReal) ∂ν := by
                    filter_upwards [hρ] with w hw
                    have hex : ∀ x, (e.symm (x,w)) i = x := by intro x; simp [e]
                    have heup : ∀ x, Function.update (e.symm (0,w)) i x = e.symm (x,w) := by
                      intro x
                      change Function.update (@Fin.insertNth n (fun _ => ℝ) i 0 w) i x = @Fin.insertNth n (fun _ => ℝ) i x w
                      exact @Fin.update_insertNth n (fun _ => ℝ) i 0 x w
                    have hz : ∀ j, 0 ≤ (e.symm (0,w)) j := by
                      intro j
                      rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩
                      · simp [e]
                      · simpa [e] using hw k
                    simp_rw [hex]
                    apply oneD M (R/(n+1 : ℝ)) R (by positivity) hR0 hdual
                      (fun x => a (e.symm (x,w)) i) (fun x => u (e.symm (x,w)) i)
                    · exact (ha i).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
                    · intro x; exact hMa _ _
                    · intro x hx
                      apply hu0
                      intro j
                      rw [← heup]
                      by_cases hji : j = i
                      · subst j; simpa using hx
                      · simpa [Function.update_of_ne hji] using hz j
                    · intro x y hx hy
                      simpa only [heup] using hic (e.symm (0,w)) i x y hz hx hy
                  calc
                    _ ≤ ∫⁻ w, ((M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ)) +
                        ENNReal.ofReal R * ∫⁻ x, (a (e.symm (x,w)) i : ENNReal) ∂ν) ∂ρ :=
                      lintegral_mono_ae hfiber
                    _ = (M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ)) +
                        ENNReal.ofReal R * ∫⁻ v, (a v i : ENNReal) ∂μ := by
                      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                        lintegral_const_mul' _ _ (by finiteness)]
                      congr 1
                      congr 1
                      exact (lintegral_prod_symm (fun z => (a (e.symm z) i : ENNReal))
                        ((hAi.comp e.symm.measurable).aemeasurable)).symm.trans (hen.lintegral_comp hAi)
                calc
                  _ = ∑ i, ∫⁻ v, ENNReal.ofReal (v i*(a v i : ℝ) - u v i) ∂μ := by
                    apply lintegral_finsetSum
                    intro i hi
                    exact (((measurable_pi_apply i).mul ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (ha i))).sub (hu i)).ennreal_ofReal
                  _ ≤ ∑ i, ((M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ)) +
                      ENNReal.ofReal R * ∫⁻ v, (a v i : ENNReal) ∂μ) := Finset.sum_le_sum fun i hi => hcoord i
                  _ = (n+1 : ℕ) * ((M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ))) +
                      ENNReal.ofReal R * ∫⁻ v, ∑ i, (a v i : ENNReal) ∂μ := by
                    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                      nsmul_eq_mul, ← Finset.mul_sum, lintegral_finsetSum]
                    intro i hi
                    exact (measurable_of_countable (fun k : ℕ => (k : ENNReal))).comp (ha i)
                  _ ≤ (M : ENNReal) * ENNReal.ofReal R + ENNReal.ofReal R * M := by
                    have heconst : ((n+1 : ℕ) : ENNReal) * ((M : ENNReal) * ENNReal.ofReal (R/(n+1 : ℝ))) =
                        (M : ENNReal) * ENNReal.ofReal R := by
                      have hn : ((n+1 : ℕ) : ENNReal) ≠ 0 := by positivity
                      have hn' : ((n+1 : ℕ) : ENNReal) ≠ ⊤ := by finiteness
                      have he : ENNReal.ofReal (n+1 : ℝ) = ((n+1 : ℕ) : ENNReal) := by norm_cast
                      rw [ENNReal.ofReal_div_of_pos hnp, he, mul_left_comm,
                        ENNReal.mul_div_cancel hn hn']
                    rw [heconst]
                    apply add_le_add_right
                    apply mul_le_mul_right
                    calc
                      _ ≤ ∫⁻ v, (M : ENNReal) ∂μ := lintegral_mono fun v => by
                        simpa only [← Nat.cast_sum] using (show ((∑ i, a v i : ℕ) : ENNReal) ≤ M by exact_mod_cast hM v)
                      _ = _ := by simp
                  _ = _ := by ring
              have mfilter : ∀ (ι : Type) [Fintype ι] (s : Finset ι)
                  (P : (Fin (n+1) → ℝ) → ι → Prop),
                  (∀ i, MeasurableSet {v | P v i}) → Measurable (fun v => s.filter (P v)) := by
                intro ι hι s P hP
                apply measurable_finset_iff.mpr
                intro i
                apply measurableSet_setOfPred.mp
                simpa only [Finset.mem_filter, Set.setOf_and] using
                  (MeasurableSet.const (i ∈ s)).inter (hP i)
              have hfin : (Finset.univ : Finset (Fin (n+1))).Nonempty := Finset.univ_nonempty
              let vmax : (Fin (n+1) → ℝ) → ℝ := fun v => Finset.univ.sup' hfin v
              have hmmax : Measurable vmax := by
                have hh : Measurable (Finset.univ.sup' hfin (fun i (v : Fin (n+1) → ℝ) => v i)) :=
                  Finset.measurable_sup' hfin (fun i hi => measurable_pi_apply i)
                convert hh using 1
                funext v
                simp only [vmax, Finset.sup'_apply]
              let F : (Fin (n+1) → ℝ) → Finset (Fin (n+1)) :=
                fun v => Finset.univ.filter (fun i => v i = vmax v)
              have hF : ∀ v, (F v).Nonempty := by
                intro v
                obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hfin v
                exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩
              let pick : Finset (Fin (n+1)) → Fin (n+1) := fun s => if h : s.Nonempty then s.min' h else 0
              let fav : (Fin (n+1) → ℝ) → Fin (n+1) := fun v => pick (F v)
              have hmf : Measurable fav := by
                apply (measurable_of_finite pick).comp
                exact mfilter _ _ _ (fun i => measurableSet_eq_fun (measurable_pi_apply i) hmmax)
              have hfmax : ∀ (v : Fin (n+1) → ℝ) j, v j ≤ v (fav v) := by
                intro v j
                have hmem : fav v ∈ F v := by simp only [fav, pick, dif_pos (hF v)]; exact Finset.min'_mem _ _
                have he := (Finset.mem_filter.mp hmem).2
                rw [he]
                exact Finset.le_sup' _ (Finset.mem_univ j)
              let b : (Fin (n+1) → ℝ) → Fin (n+1) → ℝ := fun v i =>
                Finset.univ.sup' hfin (fun j => if j = i then 0 else v j)
              have hmb : ∀ i, Measurable (fun v => b v i) := by
                intro i
                have hh : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), Measurable (fun v : Fin (n+1) → ℝ => if j = i then (0 : ℝ) else v j) := by
                  intro j hj
                  by_cases hji : j = i
                  · subst j; simpa using (measurable_const : Measurable (fun _ : Fin (n+1) → ℝ => (0 : ℝ)))
                  · simpa [hji] using measurable_pi_apply j
                have hh' := Finset.measurable_sup' hfin hh
                convert hh' using 1
                funext v
                simp only [b, Finset.sup'_apply]
              have hb0 : ∀ v i, 0 ≤ b v i := by
                intro v i
                simpa only [if_pos rfl, if_true] using
                  (Finset.le_sup' (fun j => if j = i then (0 : ℝ) else v j) (Finset.mem_univ i))
              have hble : ∀ (v : Fin (n+1) → ℝ) i j, j ≠ i → v j ≤ b v i := by
                intro v i j hji
                simpa only [if_neg hji] using
                  (Finset.le_sup' (fun j => if j = i then (0 : ℝ) else v j) (Finset.mem_univ j))
              have hbup : ∀ v i x, b (Function.update v i x) i = b v i := by
                intro v i x
                dsimp [b]
                congr 1
                funext j
                by_cases hji : j = i
                · subst j; simp
                · simp [hji]
              have hnfb : ∀ (v : Fin (n+1) → ℝ) i, fav v ≠ i → v i ≤ b v i := by
                intro v i hi
                exact (hfmax v i).trans (hble v i (fav v) hi)
              have hfb : ∀ (v : Fin (n+1) → ℝ), (∀ i, 0 ≤ v i) → b v (fav v) ≤ v (fav v) := by
                intro v hv
                apply Finset.sup'_le hfin
                intro j hj
                split_ifs
                · exact hv _
                · exact hfmax v j
              let a0 : (Fin (n+1) → ℝ) → Fin (n+1) → ℕ := fun v i => if fav v = i then 1 else 0
              let u0 : (Fin (n+1) → ℝ) → Fin (n+1) → ℝ := fun v i => max (v i - b v i) 0
              have ha0 : ∀ i, Measurable fun v => a0 v i := by
                intro i
                exact measurable_const.ite (measurableSet_eq_fun hmf measurable_const) measurable_const
              have hu0 : ∀ i, Measurable fun v => u0 v i := fun i =>
                ((measurable_pi_apply i).sub (hmb i)).max measurable_const
              have hsecond : (∫⁻ v, ENNReal.ofReal (b v (fav v)) ∂μ) ≤ 2 * ENNReal.ofReal R := by
                have hh := auction 1 a0 u0 ha0 hu0
                  (fun v => by simp [a0, Finset.sum_ite_eq'])
                  (fun v i hv => le_max_right _ _) (by
                    intro v i x y hv hx hy
                    dsimp [u0, a0]
                    simp only [Function.update_self, hbup]
                    by_cases hf : fav (Function.update v i y) = i
                    · have hyb : b v i ≤ y := by
                        have := hfb (Function.update v i y) (fun j => by
                          by_cases hji : j = i
                          · subst j; simpa using hy
                          · simpa [hji] using hv j)
                        simpa only [hf, Function.update_self, hbup] using this
                      rw [if_pos hf, Nat.cast_one, mul_one, max_eq_left (sub_nonneg.mpr hyb)]
                      exact (by linarith [le_max_left (x-b v i) 0])
                    · have hyb := hnfb (Function.update v i y) i hf
                      simp only [Function.update_self, hbup] at hyb
                      rw [if_neg hf, Nat.cast_zero, mul_zero, add_zero, max_eq_right (sub_nonpos.mpr hyb)]
                      exact le_max_right _ _)
                simp only [Nat.cast_one, mul_one] at hh
                apply le_trans ?_ hh
                apply lintegral_mono_ae
                filter_upwards [hnonneg] with v hv
                have heq : ∀ i, ENNReal.ofReal (v i*(a0 v i : ℝ) - u0 v i) =
                    if fav v = i then ENNReal.ofReal (b v i) else 0 := by
                  intro i
                  by_cases hf : fav v = i
                  · have hb := hfb v hv
                    rw [hf] at hb
                    simp [a0, u0, hf, max_eq_left (sub_nonneg.mpr hb)]
                  · have hb := hnfb v i hf
                    simp [a0, u0, hf, max_eq_right (sub_nonpos.mpr hb)]
                simp_rw [heq]
                simp
              unfold optOPQ
              refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => ?_
              unfold expOPQ
              simp only [ENNReal.ofReal_zero, zero_mul, zero_add, sub_zero, ENNReal.ofReal_one, one_mul]
              change (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ) ≤ _
              let price : Finset (Fin (n+1)) → ℝ := fun S => if S.Nonempty then opqPrice p q S else 0
              have hp0 : ∀ S, 0 ≤ price S := by
                intro S
                dsimp [price, opqPrice]
                split_ifs
                · exact hpq.1
                · exact hpq.2 _
                · rfl
              have hprice : ∀ S T, S.card = T.card → price S = price T := by
                intro S T hST
                have hh : S.Nonempty ↔ T.Nonempty := by rw [← Finset.card_pos, ← Finset.card_pos, hST]
                simp only [price, opqPrice, hST, hh]
              let L : (Fin (n+1) → ℝ) → Finset (Fin (n+1)) → ℝ := fun v S => rnValue v S - price S
              have hml : ∀ S, Measurable (fun v => L v S) := by
                intro S
                dsimp [L, rnValue]
                fun_prop
              have hall : (Finset.univ : Finset (Finset (Fin (n+1)))).Nonempty := Finset.univ_nonempty
              let U : (Fin (n+1) → ℝ) → ℝ := fun v => Finset.univ.sup' hall (L v)
              have hmU : Measurable U := by
                have hh := Finset.measurable_sup' hall (fun S hS => hml S)
                convert hh using 1
                funext v
                simp only [U, Finset.sup'_apply]
              have hUle : ∀ v S, L v S ≤ U v := fun v S => Finset.le_sup' _ (Finset.mem_univ S)
              have hU0 : ∀ v, 0 ≤ U v := by
                intro v
                simpa [L, rnValue, price] using hUle v ∅
              let W : (Fin (n+1) → ℝ) → Finset (Finset (Fin (n+1))) :=
                fun v => Finset.univ.filter (fun S => L v S = U v)
              have hW : ∀ v, (W v).Nonempty := by
                intro v
                obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup' hall (L v)
                exact ⟨S, Finset.mem_filter.mpr ⟨hS, he.symm⟩⟩
              let select : Finset (Finset (Fin (n+1))) → Finset (Fin (n+1)) := fun w =>
                if h : w.Nonempty then (Finset.exists_mem_eq_sup' h price).choose else ∅
              have hselect : ∀ w (hw : w.Nonempty), select w ∈ w ∧ w.sup' hw price = price (select w) := by
                intro w hw
                simpa only [select, dif_pos hw] using (Finset.exists_mem_eq_sup' hw price).choose_spec
              let S : (Fin (n+1) → ℝ) → Finset (Fin (n+1)) := fun v => select (W v)
              have hmS : Measurable S := by
                apply (measurable_of_finite select).comp
                exact mfilter _ _ _ (fun S => measurableSet_eq_fun (hml S) hmU)
              have hSU : ∀ v, L v (S v) = U v := by
                intro v
                exact (Finset.mem_filter.mp (hselect _ (hW v)).1).2
              have hSPmax : ∀ v T, L v T = U v → price T ≤ price (S v) := by
                intro v T hT
                rw [← (hselect _ (hW v)).2]
                exact Finset.le_sup' price (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)
              have hrev : ∀ v, opqRevenue rnValue p q v ≤ price (S v) := by
                intro v
                unfold opqRevenue menuRevenue
                simp only
                split_ifs with hw
                · obtain ⟨T, hT, heq⟩ := Finset.exists_mem_eq_sup' hw (opqPrice p q)
                  rw [heq]
                  simp only [Finset.mem_filter] at hT
                  obtain ⟨hT, hT0, hTU⟩ := hT
                  have hnT : T.Nonempty := by simpa [opqOptions] using hT
                  have hPT : price T = opqPrice p q T := by simp [price, hnT]
                  rw [← hPT]
                  apply hSPmax v T
                  apply le_antisymm (hUle v T)
                  apply Finset.sup'_le hall
                  intro A hA
                  by_cases hnA : A.Nonempty
                  · have hA' : A ∈ opqOptions (n+1) := by simpa [opqOptions] using hnA
                    simpa [L, price, hnA, hPT] using hTU A hA'
                  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnA
                    subst A
                    simpa [L, rnValue, price, hPT] using hT0
                · exact hp0 _
              have hUmono : ∀ (v w : Fin (n+1) → ℝ), (∀ i, v i ≤ w i) → U v ≤ U w := by
                intro v w hvw
                apply Finset.sup'_le hall
                intro A hA
                apply le_trans ?_ (hUle w A)
                dsimp [L, rnValue]
                apply sub_le_sub_right
                apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
                exact Finset.sum_le_sum fun i hi => hvw i
              have hreplace : ∀ (v : Fin (n+1) → ℝ) (A : Finset (Fin (n+1))) i,
                  A.Nonempty → (∀ j, v j ≤ v i) →
                  ∃ T : Finset (Fin (n+1)), i ∈ T ∧ T.card = A.card ∧ (∑ j ∈ A, v j) ≤ ∑ j ∈ T, v j := by
                intro v A i hA hi
                by_cases hiA : i ∈ A
                · exact ⟨A, hiA, rfl, le_rfl⟩
                obtain ⟨j, hj⟩ := hA
                let T := insert i (A.erase j)
                have hiE : i ∉ A.erase j := fun h => hiA (Finset.mem_of_mem_erase h)
                have hcT : T.card = A.card := by
                  rw [Finset.card_insert_of_notMem hiE, Finset.card_erase_of_mem hj]
                  have := Finset.card_pos.mpr ⟨j, hj⟩
                  omega
                refine ⟨T, Finset.mem_insert_self _ _, hcT, ?_⟩
                dsimp [T]
                rw [Finset.sum_insert hiE]
                have he := Finset.sum_erase_add A v hj
                have hv := hi j
                linarith
              have hRNup : ∀ (v : Fin (n+1) → ℝ) A i x, i ∈ A →
                  rnValue (Function.update v i x) A = rnValue v A + (x-v i)/(A.card : ℝ) := by
                intro v A i x hi
                unfold rnValue
                have he : ∑ j ∈ A, Function.update v i x j = (∑ j ∈ A, v j) + x-v i := by
                  rw [Finset.sum_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
                  have hh := Finset.sum_erase_add A v hi
                  linarith
                rw [he]
                ring
              have hslope : ∀ v i x, fav v = i → (S v).Nonempty →
                  U v + (x-v i)/((S v).card : ℝ) ≤ U (Function.update v i x) := by
                intro v i x hfi hnS
                obtain ⟨T, hiT, hcT, hsum⟩ := hreplace v (S v) i hnS (fun j => by simpa [hfi] using hfmax v j)
                have hcS : (0 : ℝ) < (S v).card := by exact_mod_cast hnS.card_pos
                have hpriceT := hprice T (S v) hcT
                have hsum' : rnValue v (S v) ≤ rnValue v T := by
                  dsimp [rnValue]
                  rw [hcT]
                  exact div_le_div_of_nonneg_right hsum hcS.le
                have h := hUle (Function.update v i x) T
                dsimp [L] at h
                rw [hRNup _ _ _ _ hiT, hcT, hpriceT] at h
                have hu := hSU v
                dsimp [L] at hu
                linarith
              let M : ℕ := (n+1).factorial
              have hMpos : 0 < M := Nat.factorial_pos _
              have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
              have hMe : (M : ENNReal) ≠ 0 := by exact_mod_cast hMpos.ne'
              have hMt : (M : ENNReal) ≠ ⊤ := by finiteness
              let a : (Fin (n+1) → ℝ) → Fin (n+1) → ℕ :=
                fun v i => if fav v = i then M/(S v).card else 0
              let u : (Fin (n+1) → ℝ) → Fin (n+1) → ℝ := fun v i =>
                (M : ℝ) * (U (Function.update v i (max (v i) (b v i))) - U (Function.update v i (b v i)))
              have hma : ∀ i, Measurable fun v => a v i := by
                intro i
                apply Measurable.ite (measurableSet_eq_fun hmf measurable_const)
                · exact (measurable_of_finite (fun T : Finset (Fin (n+1)) => M/T.card)).comp hmS
                · exact measurable_const
              have hmu : ∀ i, Measurable fun v => u v i := by
                intro i
                dsimp [u]
                apply Measurable.const_mul
                apply Measurable.sub
                · apply hmU.comp
                  apply measurable_pi_lambda
                  intro j
                  by_cases hji : j = i
                  · subst j
                    simpa only [Function.update_self] using (measurable_pi_apply i).max (hmb i)
                  · simpa only [Function.update_of_ne hji] using measurable_pi_apply j
                · apply hmU.comp
                  apply measurable_pi_lambda
                  intro j
                  by_cases hji : j = i
                  · subst j; simpa only [Function.update_self] using hmb i
                  · simpa only [Function.update_of_ne hji] using measurable_pi_apply j
              have hu_nonneg : ∀ v i, 0 ≤ u v i := by
                intro v i
                apply mul_nonneg hMr.le
                apply sub_nonneg.mpr
                apply hUmono
                intro j
                by_cases hji : j = i
                · subst j; simpa using le_max_right (v i) (b v i)
                · simp [hji]
              have hu_zero : ∀ v i, (fav v ≠ i ∨ ¬(S v).Nonempty) → u v i = 0 := by
                intro v i h
                by_cases hvi : v i ≤ b v i
                · simp [u, max_eq_right hvi]
                · have hfv : fav v = i := by
                    by_contra hh
                    exact hvi (hnfb v i hh)
                  have hSn : ¬ (S v).Nonempty := h.resolve_left (not_not.mpr hfv)
                  have hSe : S v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSn
                  have hUv : U v = 0 := by
                    have hh := hSU v
                    simpa [hSe, L, rnValue, price] using hh.symm
                  have hh : U (Function.update v i (b v i)) ≤ 0 := by
                    rw [← hUv]
                    apply hUmono
                    intro j
                    by_cases hji : j = i
                    · subst j; simpa using le_of_not_ge hvi
                    · simp [hji]
                  have hh' : U (Function.update v i (b v i)) = 0 := le_antisymm hh (hU0 _)
                  simp [u, max_eq_left (le_of_not_ge hvi), Function.update_eq_self, hUv, hh']
              have hacast : ∀ v i, fav v = i → (S v).Nonempty →
                  (a v i : ℝ) = (M : ℝ)/((S v).card : ℝ) := by
                intro v i hf hn
                simp only [a, if_pos hf]
                apply Nat.cast_div_charZero
                apply Nat.dvd_factorial hn.card_pos
                simpa only [Fintype.card_fin] using Finset.card_le_univ (S v)
              have hacap : ∀ v, ∑ i, a v i ≤ M := by
                intro v
                have he : (∑ i, a v i) = M/(S v).card := by simp [a, eq_comm]
                rw [he]
                exact Nat.div_le_self _ _
              have huIC : ∀ v i x y, (∀ j, 0 ≤ v j) → 0 ≤ x → 0 ≤ y →
                  u (Function.update v i y) i + (x-y)*(a (Function.update v i y) i : ℝ) ≤
                    u (Function.update v i x) i := by
                intro v i x y hv hx hy
                let vy := Function.update v i y
                by_cases hf : fav vy = i
                · by_cases hs : (S vy).Nonempty
                  · have hvy : ∀ j, 0 ≤ vy j := by
                      intro j
                      by_cases hji : j = i
                      · subst j; simpa [vy] using hy
                      · simpa [vy, hji] using hv j
                    have hby : b v i ≤ y := by
                      have hh := hfb vy hvy
                      rw [hf] at hh
                      simpa only [vy, Function.update_self, hbup] using hh
                    have hh := hslope vy i (max x (b v i)) hf hs
                    have hk : (0 : ℝ) < (S vy).card := by exact_mod_cast hs.card_pos
                    have hhc : (a vy i : ℝ) = (M : ℝ) / ((S vy).card : ℝ) := hacast vy i hf hs
                    have hmax := le_max_left x (b v i)
                    have hnon : 0 ≤ (max x (b v i)-x)*((M : ℝ)/((S vy).card : ℝ)) :=
                      mul_nonneg (sub_nonneg.mpr hmax) (div_nonneg hMr.le (Nat.cast_nonneg _))
                    dsimp [vy] at hh hhc
                    simp only [Function.update_self, Function.update_idem] at hh
                    dsimp [u]
                    simp only [Function.update_self, hbup, Function.update_idem]
                    rw [max_eq_left hby]
                    rw [hhc]
                    have hhm := mul_le_mul_of_nonneg_left hh hMr.le
                    dsimp [vy] at hnon
                    simp only [div_eq_mul_inv] at hhm hnon ⊢
                    nlinarith only [hhm, hnon]
                  · rw [hu_zero vy i (Or.inr hs)]
                    have hSe : S vy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
                    have ha : a vy i = 0 := by simp [a, hSe]
                    change 0 + (x-y)*(a vy i : ℝ) ≤ _
                    rw [ha, Nat.cast_zero, mul_zero, zero_add]
                    exact hu_nonneg _ _
                · rw [hu_zero vy i (Or.inl hf)]
                  have ha : a vy i = 0 := by simp [a, hf]
                  change 0 + (x-y)*(a vy i : ℝ) ≤ _
                  rw [ha, Nat.cast_zero, mul_zero, zero_add]
                  exact hu_nonneg _ _
              have hpay : (∫⁻ v, ∑ i, ENNReal.ofReal (v i*(a v i : ℝ) - u v i) ∂μ) ≤
                  2 * (M : ENNReal) * ENNReal.ofReal R :=
                auction M a u hma hmu hacap (fun v i hv => hu_nonneg v i) huIC
              let c : ℝ := 1 - 1/(n+1 : ℝ)
              have hc0 : 0 ≤ c := by
                have hh : (1 : ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
                dsimp [c]
                exact sub_nonneg.mpr ((div_le_one hnp).mpr hh)
              have hpoint : ∀ᵐ v ∂μ,
                  (M : ENNReal) * ENNReal.ofReal (opqRevenue rnValue p q v) ≤
                    (∑ i, ENNReal.ofReal (v i*(a v i : ℝ) - u v i)) +
                      ENNReal.ofReal ((M : ℝ)*c) * ENNReal.ofReal (b v (fav v)) := by
                filter_upwards [hnonneg] with v hv
                by_cases hnS : (S v).Nonempty
                · let i := fav v
                  let k := (S v).card
                  have hk0 : (0 : ℝ) < k := by exact_mod_cast hnS.card_pos
                  have hkN : (k : ℝ) ≤ n+1 := by
                    have hh : k ≤ n+1 := by simpa only [k, Fintype.card_fin] using Finset.card_le_univ (S v)
                    exact_mod_cast hh
                  have hfi : fav v = i := rfl
                  have hi_b : b v i ≤ v i := hfb v hv
                  obtain ⟨T, hiT, hcT, hsum⟩ := hreplace v (S v) i hnS (hfmax v)
                  have hsumE : (∑ j ∈ T.erase i, v j) ≤ ((T.erase i).card : ℝ)*b v i := by
                    calc
                      _ ≤ ∑ j ∈ T.erase i, b v i := Finset.sum_le_sum fun j hj =>
                        hble v i j (Finset.ne_of_mem_erase hj)
                      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
                  have hcardE : ((T.erase i).card : ℝ) = (k : ℝ)-1 := by
                    have hh : (T.erase i).card + 1 = k := by
                      simpa only [k, hcT] using Finset.card_erase_add_one hiT
                    exact_mod_cast (show ((T.erase i).card : ℤ) = (k : ℤ)-1 by omega)
                  have hsumT := Finset.sum_erase_add T v hiT
                  have havg : rnValue v (S v) ≤ v i/(k : ℝ) + (1-1/(k : ℝ))*b v i := by
                    unfold rnValue
                    change (∑ j ∈ S v, v j)/(k : ℝ) ≤ _
                    apply (div_le_iff₀ hk0).mpr
                    rw [hcardE] at hsumE
                    field_simp
                    nlinarith
                  have hfrac : 1 - 1/(k : ℝ) ≤ c := by
                    dsimp [c]
                    have := one_div_le_one_div_of_le hk0 hkN
                    linarith
                  have huval : u v i = (M : ℝ)*(U v - U (Function.update v i (b v i))) := by
                    simp only [u, max_eq_left hi_b, Function.update_eq_self]
                  have ha := hacast v i hfi hnS
                  change (a v i : ℝ) = (M : ℝ)/(k : ℝ) at ha
                  have hchosen : (M : ℝ)*price (S v) ≤
                      v i*(a v i : ℝ) - u v i + (M : ℝ)*c*b v i := by
                    have hu := hSU v
                    dsimp [L] at hu
                    rw [huval, ha]
                    have hh := mul_le_mul_of_nonneg_right hfrac (hb0 v i)
                    have hh' := hU0 (Function.update v i (b v i))
                    have hh'' := mul_le_mul_of_nonneg_left havg hMr.le
                    have hhM := mul_le_mul_of_nonneg_left hh hMr.le
                    rw [← hu]
                    simp only [div_eq_mul_inv] at hh'' hhM ⊢
                    nlinarith only [hh'', hhM, mul_nonneg hMr.le hh']
                  have hh : (M : ℝ)*opqRevenue rnValue p q v ≤
                      v i*(a v i : ℝ) - u v i + (M : ℝ)*c*b v i :=
                    (mul_le_mul_of_nonneg_left (hrev v) hMr.le).trans hchosen
                  calc
                    _ = ENNReal.ofReal ((M : ℝ)*opqRevenue rnValue p q v) := by
                      rw [ENNReal.ofReal_mul hMr.le, ENNReal.ofReal_natCast]
                    _ ≤ ENNReal.ofReal (v i*(a v i : ℝ) - u v i + (M : ℝ)*c*b v i) := ENNReal.ofReal_le_ofReal hh
                    _ ≤ ENNReal.ofReal (v i*(a v i : ℝ) - u v i) +
                        ENNReal.ofReal ((M : ℝ)*c) * ENNReal.ofReal (b v i) := by
                      rw [← ENNReal.ofReal_mul (mul_nonneg hMr.le hc0)]
                      exact ENNReal.ofReal_add_le
                    _ ≤ _ := by
                      apply add_le_add_left
                      exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (v j*(a v j : ℝ) - u v j))
                        (fun _ _ => zero_le) (Finset.mem_univ i)
                · have hSe : S v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnS
                  have hr : opqRevenue rnValue p q v ≤ 0 := by simpa [hSe, price] using hrev v
                  simp only [ENNReal.ofReal_eq_zero.mpr hr, mul_zero]
                  exact zero_le
              have hmB : Measurable (fun v => ENNReal.ofReal (b v (fav v))) := by
                have hreal : Measurable (fun v => b v (fav v)) := by
                  have he : (fun v => b v (fav v)) = fun v => ∑ i, if fav v = i then b v i else 0 := by
                    funext v
                    simp [eq_comm]
                  rw [he]
                  have hh : ∀ i, Measurable (fun v => if fav v = i then b v i else 0) := by
                    intro i
                    exact (hmb i).ite (measurableSet_eq_fun hmf measurable_const) measurable_const
                  exact Finset.measurable_sum Finset.univ (fun i hi => hh i)
                exact hreal.ennreal_ofReal
              have hbound : (M : ENNReal) * (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ) ≤
                  (M : ENNReal) * (ENNReal.ofReal (4 - 2 / ((n+1 : ℕ) : ℝ)) * optSP μ) := by
                calc
                  _ = ∫⁻ v, (M : ENNReal)*ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ := by
                    rw [lintegral_const_mul' _ _ hMt]
                  _ ≤ ∫⁻ v, (∑ i, ENNReal.ofReal (v i*(a v i : ℝ) - u v i)) +
                      ENNReal.ofReal ((M : ℝ)*c) * ENNReal.ofReal (b v (fav v)) ∂μ := lintegral_mono_ae hpoint
                  _ = (∫⁻ v, ∑ i, ENNReal.ofReal (v i*(a v i : ℝ) - u v i) ∂μ) +
                      ENNReal.ofReal ((M : ℝ)*c) * ∫⁻ v, ENNReal.ofReal (b v (fav v)) ∂μ := by
                    rw [lintegral_add_right, lintegral_const_mul _ hmB]
                    exact hmB.const_mul _
                  _ ≤ 2*(M : ENNReal)*ENNReal.ofReal R +
                      ENNReal.ofReal ((M : ℝ)*c)*(2*ENNReal.ofReal R) := by
                    exact add_le_add hpay (mul_le_mul_right hsecond _)
                  _ = _ := by
                    rw [← hR, ENNReal.ofReal_mul hMr.le, ENNReal.ofReal_natCast]
                    have hec : ENNReal.ofReal (4 - 2 / ((n+1 : ℕ) : ℝ)) = 2 + 2*ENNReal.ofReal c := by
                      have he : (4 - 2 / ((n+1 : ℕ) : ℝ)) = 2+2*c := by dsimp [c]; push_cast; ring
                      rw [he, ENNReal.ofReal_add (by norm_num) (by positivity),
                        ENNReal.ofReal_mul (by norm_num)]
                      norm_num
                    rw [hec]
                    ring
              calc
                _ = (M : ENNReal)⁻¹ * ((M : ENNReal)*(∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ)) := by
                  rw [← mul_assoc, ENNReal.inv_mul_cancel hMe hMt, one_mul]
                _ ≤ (M : ENNReal)⁻¹ * ((M : ENNReal)*(ENNReal.ofReal (4-2/((n+1 : ℕ) : ℝ))*optSP μ)) :=
                  mul_le_mul_right hbound _
                _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hMe hMt, one_mul]
