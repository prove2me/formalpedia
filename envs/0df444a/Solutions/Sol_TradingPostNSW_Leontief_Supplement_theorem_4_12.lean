-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:33.024466+00:00
-- url     : https://prove2.me/submissions/50dd2dbc-66db-4c9a-bf01-f2ca4234feae

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution :
    LinearPurityFails ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) → EnoughCompetition U →
      ∀ σ : Fin n → MeasureTheory.ProbabilityMeasure (Fin m → ℝ),
        IsMixedNE I U 0 σ → IsPure σ) ∧
    LeontiefPurityFails := by
      classical
      have hgeneral : ∀ (n m : ℕ) (I : Instance n m), GenStanding I →
          ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
          (∀ i, StrictMonoOn (U i) (box m)) → EnoughCompetition U →
          ∀ σ : Fin n → MeasureTheory.ProbabilityMeasure (Fin m → ℝ),
            IsMixedNE I U 0 σ → IsPure σ := by
        intro n m I hI U hU hstrict hec σ hσ
        cases n with
        | zero => exact fun i => Fin.elim0 i
        | succ n =>
          let A := Fin m → ℝ
          let S := Fin n → A
          have hboxzero : (0:A) ∈ box m := ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
          have hboxone : (1:A) ∈ box m := ⟨fun _ => zero_le_one, fun _ => le_rfl⟩
          let ν := fun i : Fin (n+1) =>
            MeasureTheory.Measure.pi (fun k : Fin n =>
              (σ (i.succAbove k) : MeasureTheory.Measure A))
          let P := fun (i : Fin (n+1)) (b : A) (s : S) =>
            U i (tpAlloc 0 (i.insertNth b s) i)
          let q := fun (i : Fin (n+1)) (b : A) => ∫ s, P i b s ∂ν i
          let V := fun i => expPay U 0 σ i
          have hsplit (i : Fin (n+1)) :
              MeasureTheory.Integrable (fun z : A × S => P i z.1 z.2)
                ((σ i : MeasureTheory.Measure A).prod (ν i)) := by
            have H := (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun k => (σ k : MeasureTheory.Measure A)) i).symm
            simpa [P, ν, Function.comp_def, joint,
              MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
              using H.integrable_comp_of_integrable (hσ.2.1 i)
          have hqint (i : Fin (n+1)) : MeasureTheory.Integrable (q i)
              (σ i : MeasureTheory.Measure A) := (hsplit i).integral_prod_left
          have hqeq (i : Fin (n+1)) :
              ∫ b, q i b ∂(σ i : MeasureTheory.Measure A) = V i := by
            have H := (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun k => (σ k : MeasureTheory.Measure A)) i).symm
            change (∫ b, ∫ s, P i b s ∂ν i ∂(σ i : MeasureTheory.Measure A)) = V i
            rw [← MeasureTheory.integral_prod _ (hsplit i)]
            simpa [P, ν, V, expPay, joint,
              MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
              using H.integral_comp' (fun s => U i (tpAlloc 0 s i))
          have hpure (i : Fin (n+1)) (b : A) (hb : Strategy I i b) :
              MeasureTheory.Integrable (P i b) (ν i) ∧ q i b ≤ V i := by
            have hν : MeasureTheory.Measure.pi (fun k : Fin n =>
                ((Function.update σ i (pureBid b)) (i.succAbove k) :
                  MeasureTheory.Measure A)) = ν i := by
              congr 1
              funext k
              simp [ν, Fin.succAbove_ne]
            have H := (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun k => ((Function.update σ i (pureBid b)) k :
                MeasureTheory.Measure A)) i).symm
            have hint := H.integrable_comp_of_integrable (hσ.2.2 i b hb).1
            rw [hν, Function.update_self] at hint
            have hh : MeasureTheory.Integrable (fun z : A × S => P i z.1 z.2)
                ((MeasureTheory.Measure.dirac b).prod (ν i)) := by
              simpa [P, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
                Fin.insertNthEquiv, joint, Function.update_self, pureBid] using hint
            have hpi : MeasureTheory.Integrable (P i b) (ν i) := by
              have hh' := hh.prod_right_ae
              simpa using hh'
            refine ⟨hpi, ?_⟩
            have he : expPay U 0 (Function.update σ i (pureBid b)) i = q i b := by
              have he' := H.integral_comp' (fun s => U i (tpAlloc 0 s i))
              rw [hν, Function.update_self] at he'
              have he'' : (∫ z : A × S, P i z.1 z.2
                  ∂(MeasureTheory.Measure.dirac b).prod (ν i)) =
                  expPay U 0 (Function.update σ i (pureBid b)) i := by
                simpa [P, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
                  Fin.insertNthEquiv, joint, Function.update_self, pureBid, expPay] using he'
              rw [← he'', MeasureTheory.integral_prod _ hh]
              simp only [MeasureTheory.integral_dirac]
              rfl
            simpa [he, V] using (hσ.2.2 i b hb).2
          have hbest (i : Fin (n+1)) : ∀ᵐ b ∂(σ i : MeasureTheory.Measure A),
              Strategy I i b ∧ q i b = V i := by
            have hle : q i ≤ᵐ[(σ i : MeasureTheory.Measure A)] fun _ => V i := by
              filter_upwards [hσ.1 i] with b hb using (hpure i b hb).2
            have heq := (MeasureTheory.integral_eq_iff_of_ae_le (hqint i)
              (MeasureTheory.integrable_const (V i)) hle).1 (by simpa using hqeq i)
            filter_upwards [hσ.1 i, heq] with b hb he using ⟨hb, he⟩
          have hvalid (i : Fin (n+1)) :
              ∀ᵐ s ∂ν i, ∀ k, Strategy I (i.succAbove k) (s k) := by
            apply MeasureTheory.ae_all_iff.2
            intro k
            apply MeasureTheory.ae_of_ae_map (measurable_pi_apply k).aemeasurable
            change ∀ᵐ b ∂(MeasureTheory.Measure.pi
              (fun k : Fin n => (σ (i.succAbove k) : MeasureTheory.Measure A))).map
              (Function.eval k), Strategy I (i.succAbove k) b
            rw [(MeasureTheory.measurePreserving_eval
              (fun k : Fin n => (σ (i.succAbove k) : MeasureTheory.Measure A)) k).map_eq]
            exact hσ.1 (i.succAbove k)
          have halloc (i : Fin (n+1)) (b : A) (s : S)
              (hb : Strategy I i b) (hs : ∀ k, Strategy I (i.succAbove k) (s k))
              (j : Fin m) :
              tpAlloc 0 (i.insertNth b s) i j = b j / (b j + ∑ k, s k j) := by
            have hn : ∀ k : Fin (n+1), 0 ≤ (i.insertNth (α := fun _ => A) b s k) j := by
              intro k
              obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove k
              · simpa using (hb.1 j).1
              · simpa using ((hs k).1 j).1
            have he : ∀ k : Fin (n+1), effBid 0 (i.insertNth b s) k j =
                (i.insertNth (α := fun _ => A) b s k) j := fun k => if_pos (hn k)
            simp only [tpAlloc, he, Fin.insertNth_apply_same]
            have hsum : (∑ k : Fin (n+1), (i.insertNth (α := fun _ => A) b s k) j) =
                b j + ∑ k, s k j := by
              rw [← i.add_sum_removeNth (fun k => (i.insertNth (α := fun _ => A) b s k) j)]
              simp [Fin.removeNth]
            rw [hsum]
            split_ifs with h
            · rfl
            · have hz : b j = 0 := le_antisymm (le_of_not_gt h) (hb.1 j).1
              simp [hz]
          have hbox (i : Fin (n+1)) (b : A) (s : S)
              (hb : Strategy I i b) (hs : ∀ k, Strategy I (i.succAbove k) (s k)) :
              tpAlloc 0 (i.insertNth b s) i ∈ box m := by
            constructor
            · intro j
              rw [halloc i b s hb hs j]
              exact div_nonneg (hb.1 j).1 (add_nonneg (hb.1 j).1
                (Finset.sum_nonneg fun k _ => ((hs k).1 j).1))
            · intro j
              rw [halloc i b s hb hs j]
              have hc : 0 ≤ ∑ k, s k j := Finset.sum_nonneg fun k _ => ((hs k).1 j).1
              by_cases hd : b j + ∑ k, s k j = 0
              · simp [hd]
              · apply (div_le_one
                  (lt_of_le_of_ne (add_nonneg (hb.1 j).1 hc) (Ne.symm hd))).2
                linarith
          have hshare (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) :
              (x / (x+c) + y / (y+c)) / 2 ≤ ((x+y)/2) / ((x+y)/2+c) ∧
              (0 < c → x ≠ y →
                (x / (x+c) + y / (y+c)) / 2 < ((x+y)/2) / ((x+y)/2+c)) := by
            by_cases hc0 : c = 0
            · subst c
              have hxy : 0 ≤ x+y := add_nonneg hx hy
              by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0
              · simp [hx0, hy0]
              · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
                simp [hx0, hy0, div_self (ne_of_gt hy'),
                  div_self (by positivity : y/2 ≠ 0)]
                norm_num
              · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
                simp [hx0, hy0, div_self (ne_of_gt hx'),
                  div_self (by positivity : x/2 ≠ 0)]
                norm_num
              · have hs : (x+y)/2 ≠ 0 := by positivity
                simp [hx0, hy0, hs]
            · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
              have hx' : 0 < x+c := by positivity
              have hy' : 0 < y+c := by positivity
              have hd : 0 < x+y+2*c := by positivity
              have he1 : (x/(x+c)+y/(y+c))/2 =
                  (x*(y+c)+y*(x+c))/(2*((x+c)*(y+c))) := by field_simp <;> ring
              have he2 : ((x+y)/2)/((x+y)/2+c) = (x+y)/(x+y+2*c) := by
                field_simp <;> ring
              rw [he1, he2]
              constructor
              · apply (div_le_div_iff₀ (by positivity) hd).2
                nlinarith [mul_nonneg hc (sq_nonneg (x-y))]
              · intro _ hne
                apply (div_lt_div_iff₀ (by positivity) hd).2
                have hs : 0 < (x-y)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
                nlinarith [mul_pos hc' hs]
          have hmid (i : Fin (n+1)) (b c : A) (hb : Strategy I i b) (hc : Strategy I i c) :
              Strategy I i (fun j => (b j+c j)/2) := by
            constructor
            · intro j
              constructor <;> nlinarith [(hb.1 j).1, (hb.1 j).2, (hc.1 j).1, (hc.1 j).2]
            · simp_rw [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul]
              rw [hb.2, hc.2]
              ring
          have hmidpay (i : Fin (n+1)) (b c : A) (hb : Strategy I i b) (hc : Strategy I i c)
              (s : S) (hs : ∀ k, Strategy I (i.succAbove k) (s k)) :
              (P i b s + P i c s)/2 ≤ P i (fun j => (b j+c j)/2) s ∧
              (∀ j, b j ≠ c j → 0 < ∑ k, s k j →
                (P i b s + P i c s)/2 < P i (fun j => (b j+c j)/2) s) := by
            let x := tpAlloc 0 (i.insertNth b s) i
            let y := tpAlloc 0 (i.insertNth c s) i
            let z := tpAlloc 0 (i.insertNth (fun j => (b j+c j)/2) s) i
            have hx := hbox i b s hb hs
            have hy := hbox i c s hc hs
            have hz := hbox i _ s (hmid i b c hb hc) hs
            have havg : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ box m :=
              (convex_Icc (0 : A) 1) hx hy (by norm_num) (by norm_num) (by norm_num)
            have hle : (1/2 : ℝ) • x + (1/2 : ℝ) • y ≤ z := by
              intro j
              have hh := (hshare (b j) (c j) (∑ k, s k j) (hb.1 j).1 (hc.1 j).1
                (Finset.sum_nonneg fun k _ => ((hs k).1 j).1)).1
              change (1/2 : ℝ)*x j+(1/2 : ℝ)*y j ≤ z j
              dsimp [x, y, z]
              rw [halloc i b s hb hs j, halloc i c s hc hs j,
                halloc i _ s (hmid i b c hb hc) hs j]
              convert hh using 1 <;> ring
            have hconc : (U i x + U i y)/2 ≤ U i ((1/2 : ℝ) • x + (1/2 : ℝ) • y) := by
              have hh := (hU i).1.2 hx hy (by norm_num : (0:ℝ) ≤ 1/2)
                (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
              change (1/2:ℝ)*U i x + (1/2:ℝ)*U i y ≤ _ at hh
              linarith
            refine ⟨hconc.trans ((hU i).2.1 havg hz hle), ?_⟩
            intro j hne hpos
            apply hconc.trans_lt
            apply hstrict i havg hz
            apply Pi.lt_def.2
            refine ⟨hle, j, ?_⟩
            have hh := (hshare (b j) (c j) (∑ k, s k j) (hb.1 j).1 (hc.1 j).1
              (Finset.sum_nonneg fun k _ => ((hs k).1 j).1)).2 hpos hne
            change (1/2 : ℝ)*x j+(1/2 : ℝ)*y j < z j
            dsimp [x, y, z]
            rw [halloc i b s hb hs j, halloc i c s hc hs j,
              halloc i _ s (hmid i b c hb hc) hs j]
            convert hh using 1 <;> ring
          have hstrategy (i : Fin (n+1)) (b : A) (hb : ∀ j, 0 ≤ b j)
              (hs : ∑ j, b j = I.B i) : Strategy I i b := by
            refine ⟨fun j => ⟨hb j, ?_⟩, hs⟩
            rw [← hs]
            exact Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
          have hratmono (x y c : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
              x/(x+c) ≤ y/(y+c) ∧ (0 < c → x < y → x/(x+c) < y/(y+c)) := by
            have hy : 0 ≤ y := hx.trans hxy
            constructor
            · by_cases hd : x+c = 0
              · have hx0 : x=0 := by linarith
                simp only [hx0, zero_div]
                exact div_nonneg hy (add_nonneg hy hc)
              · have hd' : 0 < x+c := lt_of_le_of_ne (add_nonneg hx hc) (Ne.symm hd)
                have hd'' : 0 < y+c := by linarith
                apply (div_le_div_iff₀ hd' hd'').2
                nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy)]
            · intro hc' hxy'
              apply (div_lt_div_iff₀ (by positivity : 0<x+c) (by positivity : 0<y+c)).2
              nlinarith [mul_pos hc' (sub_pos.mpr hxy')]
          have hratscale (a x c : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
              (hx : 0 ≤ x) (hc : 0 ≤ c) :
              a*(x/(x+c)) ≤ (a*x)/(a*x+c) := by
            rw [← mul_div_assoc]
            by_cases hd : a*x+c=0
            · have hz : a*x=0 := by nlinarith [mul_nonneg ha hx]
              simp [hz]
            · have hd' : 0<a*x+c :=
                lt_of_le_of_ne (add_nonneg (mul_nonneg ha hx) hc) (Ne.symm hd)
              apply div_le_div_of_nonneg_left (mul_nonneg ha hx) hd'
              nlinarith
          have hnozero (i : Fin (n+1)) (j : Fin m) (b : A) (hb : Strategy I i b)
              (hqb : q i b = V i) (hzero : ∀ᵐ s ∂ν i, (∑ k, s k j)=0)
              (hbj : b j=0) : False := by
            let t : ℕ → ℝ := fun r => 1/((r:ℝ)+1)
            have ht (r : ℕ) : 0 < t r ∧ t r ≤ 1 := by
              dsimp [t]
              constructor
              · positivity
              · apply (div_le_one (by positivity : (0:ℝ)<r+1)).2
                have hh : (0:ℝ) ≤ r := Nat.cast_nonneg r
                linarith
            have htlim : Filter.Tendsto t Filter.atTop (nhds 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            let d : ℕ → A := fun r k => (1-t r)*b k + if k=j then t r*I.B i else 0
            have hd (r : ℕ) : Strategy I i (d r) := by
              apply hstrategy
              · intro k
                dsimp [d]
                apply add_nonneg (mul_nonneg (sub_nonneg.mpr (ht r).2) (hb.1 k).1)
                split_ifs <;> nlinarith [hI.one_le_B i, (ht r).1]
              · simp [d, Finset.sum_add_distrib, ← Finset.mul_sum, hb.2]
                ring
            let f : ℕ → S → ℝ := fun r s => P i (d r) s
            let F : S → ℝ := fun s => ⨆ r, f r s
            have hfint (r : ℕ) : MeasureTheory.Integrable (f r) (ν i) :=
              (hpure i (d r) (hd r)).1
            have hfbound : ∀ᵐ s ∂ν i, ∀ r, 0 ≤ f r s ∧ f r s ≤ U i 1 := by
              filter_upwards [hvalid i] with s hs r
              have hx := hbox i (d r) s (hd r) hs
              exact ⟨(hU i).2.2 _ hx, (hU i).2.1 hx hboxone hx.2⟩
            have hFbound : ∀ᵐ s ∂ν i, 0 ≤ F s ∧ F s ≤ U i 1 := by
              filter_upwards [hfbound] with s hs
              have hbd : BddAbove (Set.range (fun r => f r s)) :=
                ⟨U i 1, by rintro _ ⟨r,rfl⟩; exact (hs r).2⟩
              exact ⟨(hs 0).1.trans (le_ciSup hbd 0), ciSup_le (fun r => (hs r).2)⟩
            have hFint : MeasureTheory.Integrable F (ν i) := by
              apply (MeasureTheory.integrable_const (U i 1)).mono'
                (AEMeasurable.iSup (fun r => (hfint r).aemeasurable)).aestronglyMeasurable
              filter_upwards [hFbound] with s hs
              change ‖F s‖ ≤ U i 1
              rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
              exact hs.2
            have hfmono : ∀ᵐ s ∂ν i, Monotone (fun r => f r s) := by
              filter_upwards [hvalid i, hzero] with s hs hz r r' hrr
              change (∑ k, s k j)=0 at hz
              apply (hU i).2.1 (hbox i _ s (hd r) hs) (hbox i _ s (hd r') hs)
              intro k
              rw [halloc i _ s (hd r) hs k, halloc i _ s (hd r') hs k]
              have htr : t r' ≤ t r := by
                dsimp [t]
                apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<r+1)
                exact_mod_cast Nat.add_le_add_right hrr 1
              by_cases hkj : k=j
              · subst k
                simp only [d, hbj, mul_zero, ite_true, zero_add, hz, add_zero]
                rw [div_self (by nlinarith [hI.one_le_B i, (ht r).1] : t r*I.B i ≠ 0),
                  div_self (by nlinarith [hI.one_le_B i, (ht r').1] : t r'*I.B i ≠ 0)]
              · exact (hratmono (d r k) (d r' k) (∑ k', s k' k) ((hd r).1 k).1
                  (by dsimp [d]; simp only [if_neg hkj, add_zero]; nlinarith [(hb.1 k).1])
                  (Finset.sum_nonneg fun k' _ => ((hs k').1 k).1)).1
            have hflim : ∀ᵐ s ∂ν i,
                Filter.Tendsto (fun r => f r s) Filter.atTop (nhds (F s)) := by
              filter_upwards [hfmono, hfbound] with s hs hbnd
              exact tendsto_atTop_ciSup hs
                ⟨U i 1, by rintro _ ⟨r,rfl⟩; exact (hbnd r).2⟩
            have hFlim :=
              MeasureTheory.integral_tendsto_of_tendsto_of_monotone hfint hFint hfmono hflim
            have hFle : (∫ s, F s ∂ν i) ≤ V i :=
              le_of_tendsto hFlim
                (Filter.Eventually.of_forall (fun r => (hpure i (d r) (hd r)).2))
            have hFgt : ∀ᵐ s ∂ν i, P i b s < F s := by
              filter_upwards [hvalid i, hzero, hfbound] with s hs hz hfb
              change (∑ k, s k j)=0 at hz
              let x := tpAlloc 0 (i.insertNth b s) i
              let y := Function.update x j 1
              have hx := hbox i b s hb hs
              have hxj : x j=0 := by
                dsimp [x]
                rw [halloc i b s hb hs j, hbj]
                simp
              have hy : y ∈ box m := by
                constructor <;> intro k <;> by_cases hkj : k=j
                · subst k; simp [y]
                · simpa [y, hkj] using hx.1 k
                · subst k; simp [y]
                · simpa [y, hkj] using hx.2 k
              have hxy : x < y := Pi.lt_def.2 ⟨by
                  intro k
                  by_cases hkj : k=j
                  · subst k; simp [y, hxj]
                  · simp [y, hkj], j, by simp [y, hxj]⟩
              have huy : U i x < U i y := hstrict i hx hy hxy
              have hbd : BddAbove (Set.range (fun r => f r s)) :=
                ⟨U i 1, by rintro _ ⟨r,rfl⟩; exact (hfb r).2⟩
              have hlow (r : ℕ) : (1-t r)*U i y + t r*U i 0 ≤ f r s := by
                have hconv : (1-t r) • y + t r • (0:A) ∈ box m :=
                  (convex_Icc (0:A) 1) hy hboxzero
                    (sub_nonneg.mpr (ht r).2) (ht r).1.le (by ring)
                have hle : (1-t r) • y + t r • (0:A) ≤
                    tpAlloc 0 (i.insertNth (d r) s) i := by
                  intro k
                  change (1-t r)*y k+t r*0 ≤ _
                  rw [halloc i _ s (hd r) hs k]
                  by_cases hkj : k=j
                  · subst k
                    simp only [y, Function.update_self, d, hbj, mul_zero, ite_true, zero_add,
                      hz, add_zero, mul_one]
                    rw [div_self (by nlinarith [hI.one_le_B i, (ht r).1] : t r*I.B i ≠ 0)]
                    nlinarith [(ht r).1]
                  · simp only [y, Function.update_of_ne hkj, x, d, if_neg hkj, add_zero, mul_zero]
                    rw [halloc i b s hb hs k]
                    exact hratscale (1-t r) (b k) (∑ k', s k' k) (sub_nonneg.mpr (ht r).2)
                      (by linarith [(ht r).1]) (hb.1 k).1
                      (Finset.sum_nonneg fun k' _ => ((hs k').1 k).1)
                have hcon := (hU i).1.2 hy hboxzero
                  (sub_nonneg.mpr (ht r).2) (ht r).1.le (show (1-t r)+t r=1 by ring)
                exact hcon.trans ((hU i).2.1 hconv (hbox i _ s (hd r) hs) hle)
              have hylow : U i y ≤ F s := by
                have hlim : Filter.Tendsto (fun r => (1-t r)*U i y+t r*U i 0)
                    Filter.atTop (nhds (U i y)) := by
                  convert ((tendsto_const_nhds.sub htlim).mul_const (U i y)).add
                    (htlim.mul_const (U i 0)) using 1 <;> simp
                exact le_of_tendsto hlim
                  (Filter.Eventually.of_forall fun r => (hlow r).trans (le_ciSup hbd r))
              exact huy.trans_le hylow
            have hle : P i b ≤ᵐ[ν i] F := hFgt.mono (fun _ h => h.le)
            have heqint : (∫ s, P i b s ∂ν i) = ∫ s, F s ∂ν i := by
              apply le_antisymm (MeasureTheory.integral_mono_ae (hpure i b hb).1 hFint hle)
              simpa [← hqb] using hFle
            have heq :=
              (MeasureTheory.integral_eq_iff_of_ae_le (hpure i b hb).1 hFint hle).1 heqint
            obtain ⟨s, hs, he⟩ := (hFgt.and heq).exists
            exact (ne_of_lt hs) he
          have hcomp : ∀ (i : Fin (n+1)) (j : Fin m),
              ¬ ∀ᵐ s ∂ν i, (∑ k, s k j) = 0 := by
            intro i j hz
            have hn : 0<n := by
              by_contra h
              have hn0 : n=0 := Nat.eq_zero_of_not_pos h
              subst n
              obtain ⟨a,k,hak,_⟩ := hec ⟨0,hI.pos_m⟩
              exact hak (Fin.ext (by omega))
            obtain ⟨b,hb,hqb⟩ := (hbest i).exists
            by_cases hbj : b j=0
            · exact hnozero i j b hb hqb hz hbj
            have hbjpos : 0<b j := lt_of_le_of_ne (hb.1 j).1 (Ne.symm hbj)
            obtain ⟨l,hl⟩ : ∃ l : Fin m, ¬ ∀ᵐ s ∂ν i, (∑ k, s k l)=0 := by
              by_contra! hall
              have hall' := MeasureTheory.ae_all_iff.2 hall
              obtain ⟨s,hs,hsz⟩ := ((hvalid i).and hall').exists
              let k : Fin n := ⟨0,hn⟩
              have hz' (l : Fin m) : s k l=0 := by
                apply le_antisymm _ ((hs k).1 l).1
                have hh := Finset.single_le_sum
                  (fun k' (_ : k' ∈ Finset.univ) => ((hs k').1 l).1) (Finset.mem_univ k)
                rw [hsz l] at hh
                exact hh
              have hb0 : I.B (i.succAbove k)=0 := by
                rw [← (hs k).2]
                simp [hz']
              have hh := hI.one_le_B (i.succAbove k)
              linarith
            have hlj : l≠j := by intro h; subst l; exact hl hz
            have hjl : j≠l := Ne.symm hlj
            let c : A := fun k => b k + (if k=l then b j/2 else 0) -
              (if k=j then b j/2 else 0)
            have hcj : c j=b j/2 := by dsimp [c]; simp [hjl]; ring
            have hcl : c l=b l+b j/2 := by simp [c,hlj]
            have hck (k : Fin m) (hk : k≠j) : b k ≤ c k := by
              dsimp [c]
              simp only [if_neg hk, sub_zero]
              split_ifs <;> linarith
            have hc : Strategy I i c := by
              apply hstrategy
              · intro k
                by_cases hk : k=j
                · subst k; rw [hcj]; positivity
                · exact (hb.1 k).1.trans (hck k hk)
              · simp [c, Finset.sum_sub_distrib, Finset.sum_add_distrib, hb.2]
            have hpay (s : S) (hs : ∀ k, Strategy I (i.succAbove k) (s k))
                (hsz : (∑ k, s k j)=0) :
                P i b s ≤ P i c s ∧ (0 < ∑ k, s k l → P i b s < P i c s) := by
              have hle : tpAlloc 0 (i.insertNth b s) i ≤ tpAlloc 0 (i.insertNth c s) i := by
                intro k
                rw [halloc i b s hb hs k, halloc i c s hc hs k]
                by_cases hk : k=j
                · subst k
                  rw [hcj, hsz]
                  simp [hbj, (by positivity : b j/2 ≠ 0)]
                · exact (hratmono (b k) (c k) (∑ k',s k' k) (hb.1 k).1 (hck k hk)
                    (Finset.sum_nonneg fun k' _ => ((hs k').1 k).1)).1
              refine ⟨(hU i).2.1 (hbox i b s hb hs) (hbox i c s hc hs) hle, ?_⟩
              intro hp
              apply hstrict i (hbox i b s hb hs) (hbox i c s hc hs)
              apply Pi.lt_def.2
              refine ⟨hle,l,?_⟩
              rw [halloc i b s hb hs l, halloc i c s hc hs l]
              exact (hratmono (b l) (c l) (∑ k',s k' l) (hb.1 l).1 (hck l hlj)
                (Finset.sum_nonneg fun k' _ => ((hs k').1 l).1)).2 hp (by rw [hcl]; linarith)
            have hle : P i b ≤ᵐ[ν i] P i c := by
              filter_upwards [hvalid i, hz] with s hs hsz using (hpay s hs hsz).1
            have he : q i b=q i c := by
              apply le_antisymm
                (MeasureTheory.integral_mono_ae (hpure i b hb).1 (hpure i c hc).1 hle)
              change q i c ≤ q i b
              rw [hqb]
              exact (hpure i c hc).2
            have heq :=
              (MeasureTheory.integral_eq_iff_of_ae_le (hpure i b hb).1 (hpure i c hc).1 hle).1 he
            apply hl
            filter_upwards [hvalid i, hz, heq] with s hs hsz heq
            have hnon : 0 ≤ ∑ k, s k l := Finset.sum_nonneg fun k _ => ((hs k).1 l).1
            by_contra hnot
            exact (ne_of_lt ((hpay s hs hsz).2 (lt_of_le_of_ne hnon (Ne.symm hnot)))) heq
          intro i
          obtain ⟨b, hb, hqb⟩ := (hbest i).exists
          refine ⟨b, ?_⟩
          have hconst : ∀ᵐ c ∂(σ i : MeasureTheory.Measure A), c = b := by
            filter_upwards [hbest i] with c hc
            by_contra hne
            obtain ⟨j, hj⟩ : ∃ j, b j ≠ c j := by
              by_contra h
              apply hne
              funext j
              exact (not_exists_not.1 h j).symm
            let d : A := fun j => (b j+c j)/2
            have hd := hmid i b c hb hc.1
            have hint : MeasureTheory.Integrable (fun s => (P i b s+P i c s)/2) (ν i) :=
              ((hpure i b hb).1.add (hpure i c hc.1).1).div_const 2
            have hle : (fun s => (P i b s+P i c s)/2) ≤ᵐ[ν i] P i d := by
              filter_upwards [hvalid i] with s hs using (hmidpay i b c hb hc.1 s hs).1
            have he : (∫ s, (P i b s+P i c s)/2 ∂ν i) = q i d := by
              apply le_antisymm
              · exact MeasureTheory.integral_mono_ae hint (hpure i d hd).1 hle
              · have hv := (hpure i d hd).2
                rw [MeasureTheory.integral_div, MeasureTheory.integral_add
                  (hpure i b hb).1 (hpure i c hc.1).1]
                change q i d ≤ (q i b+q i c)/2
                rw [hqb, hc.2]
                linarith
            have heq :=
              (MeasureTheory.integral_eq_iff_of_ae_le hint (hpure i d hd).1 hle).1 he
            apply hcomp i j
            filter_upwards [hvalid i, heq] with s hs heq
            have hn : 0 ≤ ∑ k, s k j := Finset.sum_nonneg fun k _ => ((hs k).1 j).1
            by_contra hnot
            have hp : 0 < ∑ k, s k j := lt_of_le_of_ne hn (Ne.symm hnot)
            exact (ne_of_lt ((hmidpay i b c hb hc.1 s hs).2 j hj hp)) heq
          apply Subtype.ext
          change (σ i : MeasureTheory.Measure A) = MeasureTheory.Measure.dirac b
          have hid : MeasureTheory.Measure.map (fun c : A => c) (σ i : MeasureTheory.Measure A) =
              MeasureTheory.Measure.map (fun _ : A => b) (σ i : MeasureTheory.Measure A) :=
            MeasureTheory.Measure.map_congr hconst
          have hu : (σ i : MeasureTheory.Measure A) Set.univ=1 := (σ i).property.measure_univ
          simpa [hu] using hid
      let mix := fun {m : ℕ} (a b : Fin m → ℝ) =>
        (⟨(1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b, by
          apply MeasureTheory.isProbabilityMeasure_iff.2
          norm_num
          exact ENNReal.inv_two_add_inv_two⟩ : MeasureTheory.ProbabilityMeasure (Fin m → ℝ))
      have hdirac (n m : ℕ) (c : Fin n → Fin m → ℝ) :
          joint (fun k => pureBid (c k)) = MeasureTheory.Measure.dirac c := by
        have he (i : Fin n) : ∀ᵐ s ∂joint (fun k => pureBid (c k)), s i=c i := by
          apply MeasureTheory.ae_of_ae_map (f := fun s : Fin n → Fin m → ℝ => s i)
            (μ := joint (fun k => pureBid (c k))) (p := fun b : Fin m → ℝ => b=c i)
            (measurable_pi_apply i).aemeasurable
          change ∀ᵐ s ∂(MeasureTheory.Measure.pi (fun k =>
            (pureBid (c k) : MeasureTheory.Measure (Fin m → ℝ)))).map (Function.eval i), s=c i
          rw [(MeasureTheory.measurePreserving_eval
            (fun k => (pureBid (c k) : MeasureTheory.Measure (Fin m → ℝ))) i).map_eq]
          simp [pureBid]
        have hc : ∀ᵐ s ∂joint (fun k => pureBid (c k)), s=c := by
          filter_upwards [MeasureTheory.ae_all_iff.2 he] with s hs
          funext i
          exact hs i
        haveI : MeasureTheory.IsProbabilityMeasure (joint (fun k => pureBid (c k))) := by
          dsimp [joint]
          infer_instance
        have HH : (joint (fun k => pureBid (c k))).map (fun s => s) =
            (joint (fun k => pureBid (c k))).map (fun _ => c) :=
          MeasureTheory.Measure.map_congr hc
        simpa using HH
      have hmixjoint (n m : ℕ) (a b : Fin m → ℝ) (c : Fin n → Fin m → ℝ) :
          joint (Fin.cons (mix a b) (fun k => pureBid (c k))) =
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac (Fin.cons a c) +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac (Fin.cons b c) := by
        let σ : Fin (n+1) → MeasureTheory.ProbabilityMeasure (Fin m → ℝ) :=
          Fin.cons (mix a b) (fun k => pureBid (c k))
        have H := (MeasureTheory.measurePreserving_piFinSuccAbove
          (fun k => (σ k : MeasureTheory.Measure (Fin m → ℝ))) 0).symm
        have hν : MeasureTheory.Measure.pi (fun k : Fin n =>
            (σ ((0 : Fin (n+1)).succAbove k) : MeasureTheory.Measure (Fin m → ℝ))) =
            MeasureTheory.Measure.dirac c := by
          have heσ (k : Fin n) : σ ((0:Fin (n+1)).succAbove k)=pureBid (c k) := by rfl
          simp_rw [heσ]
          exact hdirac n m c
        change joint σ = _
        rw [show joint σ = _ from H.map_eq.symm, hν]
        have hσ0 : (σ 0 : MeasureTheory.Measure (Fin m → ℝ)) =
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b := rfl
        rw [hσ0]
        rw [MeasureTheory.Measure.add_prod]
        simp only [MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.dirac_prod_dirac]
        rw [MeasureTheory.Measure.map_add _ _ (by fun_prop)]
        simp [MeasureTheory.Measure.map_smul, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
      have hupdate (n m : ℕ) (σ : Fin n → MeasureTheory.ProbabilityMeasure (Fin m → ℝ))
          (i : Fin n) (d : Fin m → ℝ) :
          joint (Function.update σ i (pureBid d)) =
            (joint σ).map (fun s => Function.update s i d) := by
        let f : Fin n → (Fin m → ℝ) → (Fin m → ℝ) := fun k x => if k=i then d else x
        have hf (k : Fin n) : Measurable (f k) := by
          dsimp [f]
          split_ifs <;> fun_prop
        have hm (k : Fin n) : (σ k : MeasureTheory.Measure (Fin m → ℝ)).map (f k) =
            ((Function.update σ i (pureBid d)) k : MeasureTheory.Measure (Fin m → ℝ)) := by
          by_cases hk : k=i
          · subst k
            rw [Function.update_self]
            simp [f, pureBid]
          · simp [f, hk]
        haveI (k : Fin n) : MeasureTheory.IsProbabilityMeasure
            ((σ k : MeasureTheory.Measure (Fin m → ℝ)).map (f k)) := by
          rw [hm k]
          infer_instance
        have hh := MeasureTheory.Measure.pi_map_pi
          (μ := fun k => (σ k : MeasureTheory.Measure (Fin m → ℝ))) (f := f)
          (fun k => (hf k).aemeasurable)
        have he : (fun s k => f k (s k)) = (fun s => Function.update s i d) := by
          funext s k
          by_cases hk : k=i <;> simp [f, hk]
        rw [he] at hh
        simpa only [hm, joint] using hh.symm
      have hmean (n m : ℕ) (a b : Fin n → Fin m → ℝ)
          (f : (Fin n → Fin m → ℝ) → ℝ) :
          MeasureTheory.Integrable f ((1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b) ∧
          (∫ s, f s ∂((1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b)) = (f a+f b)/2 := by
        have ha : MeasureTheory.Integrable f ((1/2 : ENNReal) • MeasureTheory.Measure.dirac a) :=
          (MeasureTheory.integrable_dirac (by finiteness)).smul_measure (by norm_num)
        have hb : MeasureTheory.Integrable f ((1/2 : ENNReal) • MeasureTheory.Measure.dirac b) :=
          (MeasureTheory.integrable_dirac (by finiteness)).smul_measure (by norm_num)
        refine ⟨ha.add_measure hb, ?_⟩
        rw [MeasureTheory.integral_add_measure ha hb]
        simp only [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
          ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
        ring
      have hne (n m : ℕ) (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ) (Δ : ℝ)
          (σ : Fin n → MeasureTheory.ProbabilityMeasure (Fin m → ℝ)) (a b : Fin n → Fin m → ℝ)
          (hjoint : joint σ = (1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b)
          (ha : ∀ i, Strategy I i (a i)) (hb : ∀ i, Strategy I i (b i))
          (hbr : ∀ i d, Strategy I i d →
            (U i (tpAlloc Δ (Function.update a i d) i) +
              U i (tpAlloc Δ (Function.update b i d) i))/2 ≤
            (U i (tpAlloc Δ a i)+U i (tpAlloc Δ b i))/2) : IsMixedNE I U Δ σ := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          rw [← (MeasureTheory.measurePreserving_eval
            (fun k => (σ k : MeasureTheory.Measure (Fin m → ℝ))) i).map_eq]
          have hmeas : MeasurableSet {b : Fin m → ℝ | Strategy I i b} := by
            have hh : MeasurableSet ((⋂ j : Fin m, {b : Fin m → ℝ | 0≤b j ∧ b j≤I.B i}) ∩
                {b : Fin m → ℝ | ∑ j,b j=I.B i}) :=
              (MeasurableSet.iInter fun j =>
                (measurableSet_le measurable_const (measurable_pi_apply j)).inter
                  (measurableSet_le (measurable_pi_apply j) measurable_const)).inter
                (measurableSet_eq_fun (by fun_prop) measurable_const)
            have he : {b : Fin m → ℝ | Strategy I i b} =
                ((⋂ j : Fin m, {b : Fin m → ℝ | 0≤b j ∧ b j≤I.B i}) ∩
                  {b : Fin m → ℝ | ∑ j,b j=I.B i}) := by
              ext b
              simp [Strategy]
            exact he.symm ▸ hh
          apply (MeasureTheory.ae_map_iff (f := fun s : Fin n → Fin m → ℝ => s i)
            (measurable_pi_apply i).aemeasurable hmeas).2
          change ∀ᵐ s ∂joint σ, Strategy I i (s i)
          rw [hjoint]
          simp [ha i, hb i]
        · intro i
          rw [hjoint]
          exact (hmean n m a b (fun s => U i (tpAlloc Δ s i))).1
        · intro i d hd
          have hj : joint (Function.update σ i (pureBid d)) =
              (1/2 : ENNReal) • MeasureTheory.Measure.dirac (Function.update a i d) +
              (1/2 : ENNReal) • MeasureTheory.Measure.dirac (Function.update b i d) := by
            rw [hupdate, hjoint]
            rw [MeasureTheory.Measure.map_add _ _ (by fun_prop)]
            simp [MeasureTheory.Measure.map_smul]
          refine ⟨by rw [hj]; exact (hmean n m _ _ (fun s => U i (tpAlloc Δ s i))).1, ?_⟩
          unfold expPay
          rw [hj, hjoint, (hmean n m _ _ (fun s => U i (tpAlloc Δ s i))).2,
            (hmean n m _ _ (fun s => U i (tpAlloc Δ s i))).2]
          exact hbr i d hd
      have hnotpure (n m : ℕ)
          (σ : Fin (n+1) → MeasureTheory.ProbabilityMeasure (Fin m → ℝ))
          (a b : Fin m → ℝ) (hab : a≠b)
          (hzero : (σ 0 : MeasureTheory.Measure (Fin m → ℝ)) =
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac a +
            (1/2 : ENNReal) • MeasureTheory.Measure.dirac b) : ¬ IsPure σ := by
        intro h
        obtain ⟨d,hd⟩ := h 0
        have hm : (σ 0 : MeasureTheory.Measure (Fin m → ℝ)) {a} = (1/2 : ENNReal) := by
          rw [hzero]
          simp [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
            MeasureTheory.Measure.dirac_apply, Ne.symm hab]
        have he := congrArg (fun μ : MeasureTheory.ProbabilityMeasure (Fin m → ℝ) =>
          (μ : MeasureTheory.Measure (Fin m → ℝ)) {a}) hd
        rw [hm] at he
        have hhalf0 : (1/2 : ENNReal) ≠ 0 := by simp
        have hhalf1 : (1/2 : ENNReal) ≠ 1 := by
          intro hh
          have hh' := congrArg (fun x : ENNReal => x⁻¹) hh
          norm_num at hh'
        by_cases hda : d=a
        · exact hhalf1 (by simpa [pureBid, MeasureTheory.Measure.dirac_apply, hda] using he)
        · exact hhalf0 (by simpa [pureBid, MeasureTheory.Measure.dirac_apply, hda] using he)
      have hupdatevalid {n m : ℕ} (I : Instance n m) (a : Fin n → Fin m → ℝ)
          (ha : ∀ i, Strategy I i (a i)) (i : Fin n) (d : Fin m → ℝ) (hd : Strategy I i d) :
          ∀ k, Strategy I k ((Function.update a i d) k) := by
        intro k
        by_cases hk : k=i
        · subst k; simpa using hd
        · simpa [Function.update_of_ne hk] using ha k
      have hleo : LeontiefPurityFails := by
        let I := feeRefutationInstance
        let a : Fin 2 → ℝ := fun j => if j=0 then 1 else 0
        let b : Fin 2 → ℝ := fun j => if j=0 then 0 else 1
        let c : Fin 1 → Fin 2 → ℝ := fun _ => a
        let p : Fin 2 → Fin 2 → ℝ := Fin.cons a c
        let r : Fin 2 → Fin 2 → ℝ := Fin.cons b c
        let σ : Fin 2 → MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ) :=
          Fin.cons (mix a b) (fun k => pureBid (c k))
        have ha : ∀ i, Strategy I i (p i) := by
          intro i
          fin_cases i <;> constructor
          all_goals first
            | (intro j; fin_cases j <;> norm_num [I,feeRefutationInstance,p,c,a])
            | norm_num [I,feeRefutationInstance,p,c,a,Fin.sum_univ_two]
        have hb : ∀ i, Strategy I i (r i) := by
          intro i
          fin_cases i <;> constructor
          all_goals first
            | (intro j; fin_cases j <;> norm_num [I,feeRefutationInstance,r,c,a,b])
            | norm_num [I,feeRefutationInstance,r,c,a,b,Fin.sum_univ_two]
        have hzero (s : Fin 2 → Fin 2 → ℝ) (hs : ∀ i, Strategy I i (s i)) (i : Fin 2) :
            tpAlloc 2 s i=0 := by
          funext j
          have hbid : s i j ≤ 1 := ((hs i).1 j).2
          have he : effBid 2 s i j=0 := by
            apply if_neg
            change ¬ 2 ≤ s i j
            linarith
          simp [tpAlloc,he]
        have hu0 (i : Fin 2) : u I i 0=0 := by
          unfold u
          split_ifs <;> simp
        have hpayzero (s : Fin 2 → Fin 2 → ℝ) (hs : ∀ i, Strategy I i (s i)) (i : Fin 2) :
            u I i (tpAlloc 2 s i)=0 := by
          rw [hzero s hs i]
          exact hu0 i
        change Standing I ∧ PerfectCompetition I ∧ _
        refine ⟨?_, ?_, σ, ?_, ?_⟩
        · refine ⟨by norm_num, ?_, ?_, ?_⟩
          · intro i j; norm_num [I,feeRefutationInstance]
          · intro i; norm_num [I,feeRefutationInstance]
          · intro i; exact ⟨0,by simp [D,I,feeRefutationInstance]⟩
        · intro j
          exact ⟨0,1,by decide,by norm_num [I,feeRefutationInstance],
            by norm_num [I,feeRefutationInstance]⟩
        · apply hne 2 2 I (u I) 2 σ p r (hmixjoint 1 2 a b c) ha hb
          intro i d hd
          rw [hpayzero p ha i, hpayzero r hb i,
            hpayzero _ (hupdatevalid I p ha i d hd) i,
            hpayzero _ (hupdatevalid I r hb i d hd) i]
        · apply hnotpure 1 2 σ a b
          · intro h
            have hh := congrFun h 0
            norm_num [a,b] at hh
          · rfl
      have hlinear : LinearPurityFails := by
        let I := linearRefutationInstance
        let a : ℝ → Fin 2 → ℝ := fun t j => if j=0 then t else 1-t
        let c : Fin 2 → Fin 2 → ℝ := fun _ j => if j=0 then 0 else 1
        let p : ℝ → Fin 3 → Fin 2 → ℝ := fun t => Fin.cons (a t) c
        let σ : Fin 3 → MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ) :=
          Fin.cons (mix (a 1) (a (1/2))) (fun k => pureBid (c k))
        have hpval (t : ℝ) (i : Fin 3) (j : Fin 2) :
            p t i j = if i=0 then a t j else c 0 j := by
          cases i using Fin.cases with
          | zero => simp [p]
          | succ k => simp [p,c]
        have h20 : (2:Fin 3)≠0 := by decide
        have h21 : (2:Fin 3)≠1 := by decide
        have hp (t : ℝ) (ht : t=1 ∨ t=1/2) : ∀ i, Strategy I i (p t i) := by
          intro i
          rcases ht with rfl | rfl <;> fin_cases i <;> constructor
          all_goals first
            | (intro j; fin_cases j <;> norm_num [hpval,h20,h21,I,linearRefutationInstance,a,c])
            | norm_num [hpval,h20,h21,I,linearRefutationInstance,a,c,Fin.sum_univ_two]
        have halloc (s : Fin 3 → Fin 2 → ℝ) (hs : ∀ i, Strategy I i (s i))
            (i : Fin 3) (j : Fin 2) : tpAlloc 0 s i j=s i j/(∑ k,s k j) := by
          have he (k : Fin 3) : effBid 0 s k j=s k j := if_pos ((hs k).1 j).1
          simp only [tpAlloc,he]
          split_ifs with h
          · rfl
          · have hz : s i j=0 := le_antisymm (le_of_not_gt h) ((hs i).1 j).1
            simp [hz]
        have hpay (s : Fin 3 → Fin 2 → ℝ) (hs : ∀ i, Strategy I i (s i)) (i : Fin 3) :
            linU I i (tpAlloc 0 s i)= ∑ j,I.v i j*(s i j/(∑ k,s k j)) := by
          unfold linU
          congr 1
          ext j
          rw [halloc s hs i j]
        have hself (x : ℝ) : x/x ≤ 1 := by
          by_cases hx : x=0 <;> simp [hx]
        have hfrac (x c : ℝ) (hx0 : 0≤x) (hx1 : x≤1) (hc : 0<c) :
            x/(x+c) ≤ 1/(1+c) := by
          apply (div_le_div_iff₀ (by positivity : 0<x+c) (by positivity : 0<1+c)).2
          nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hx1)]
        have hval1 (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x+y=1) :
            (1/10:ℝ)*(x/(x+1))+y/(y+1) ≤ 1/2 := by
          have he : (1/10:ℝ)*(x/(x+1))+y/(y+1) =
              (x*(y+1)+10*y*(x+1))/(10*((x+1)*(y+1))) := by field_simp <;> ring
          rw [he]
          apply (div_le_iff₀ (by positivity : 0<10*((x+1)*(y+1)))).2
          have hy' : y=1-x := by linarith
          rw [hy']
          nlinarith [sq_nonneg x]
        have hval2 (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x+y=1) :
            (1/10:ℝ)*(x/(x+1/2))+y/(y+3/2) ≤ 2/5 := by
          have he : (1/10:ℝ)*(x/(x+1/2))+y/(y+3/2) =
              (x*(y+3/2)+10*y*(x+1/2))/(10*((x+1/2)*(y+3/2))) := by
            field_simp <;> ring
          rw [he]
          apply (div_le_iff₀ (by positivity : 0<10*((x+1/2)*(y+3/2)))).2
          have hy' : y=1-x := by linarith
          rw [hy']
          nlinarith [sq_nonneg x]
        have hbr (t : ℝ) (ht : t=1 ∨ t=1/2) (i : Fin 3) (d : Fin 2 → ℝ)
            (hd : Strategy I i d) :
            linU I i (tpAlloc 0 (Function.update (p t) i d) i) ≤
              linU I i (tpAlloc 0 (p t) i) := by
          have hx : 0≤d 0 := (hd.1 0).1
          have hy : 0≤d 1 := (hd.1 1).1
          have hy1 : d 1≤1 := (hd.1 1).2
          have hxy : d 0+d 1=1 := by
            simpa [I,linearRefutationInstance,Fin.sum_univ_two] using hd.2
          have hupd (k : Fin 3) (j : Fin 2) :
              (Function.update (p t) i d) k j = if k.val=i.val then d j else p t k j := by
            by_cases hk : k=i
            · subst k; simp
            · have hv : k.val≠i.val := fun h => hk (Fin.ext h)
              simp [Function.update_of_ne hk,hv]
          rw [hpay _ (hupdatevalid I (p t) (hp t ht) i d hd) i, hpay _ (hp t ht) i]
          simp_rw [hupd]
          rcases ht with rfl | rfl <;> fin_cases i
          all_goals norm_num [Fin.val_ofNat,hpval,h20,h21,I,linearRefutationInstance,
            a,c,Fin.sum_univ_succ,Function.update_apply]
          · exact hself (d 0)
          · convert hval1 (d 0) (d 1) hx hy hxy using 1 <;> ring
          · convert hfrac (d 1) 1 hy hy1 (by norm_num) using 1 <;> ring
          · exact hself (d 0)
          · convert hval2 (d 0) (d 1) hx hy hxy using 1 <;> ring
          · convert hfrac (d 1) (3/2) hy hy1 (by norm_num) using 1 <;> ring
        change LinStanding I ∧ PerfectCompetition I ∧ (∀ i, ∃ j, 0<I.v i j) ∧ _
        refine ⟨?_,?_,?_,σ,?_,?_⟩
        · refine ⟨by norm_num, ?_, ?_⟩
          · intro i j
            fin_cases i <;> fin_cases j <;> norm_num [h20,h21,I,linearRefutationInstance]
          · intro i; norm_num [h20,h21,I,linearRefutationInstance]
        · intro j
          fin_cases j
          · exact ⟨0,1,by decide,by norm_num [h20,h21,I,linearRefutationInstance],
              by norm_num [h20,h21,I,linearRefutationInstance]⟩
          · exact ⟨1,2,by decide,by norm_num [h20,h21,I,linearRefutationInstance],
              by norm_num [h20,h21,I,linearRefutationInstance]⟩
        · intro i
          fin_cases i
          · exact ⟨0,by norm_num [h20,h21,I,linearRefutationInstance]⟩
          · exact ⟨1,by norm_num [h20,h21,I,linearRefutationInstance]⟩
          · exact ⟨1,by norm_num [h20,h21,I,linearRefutationInstance]⟩
        · apply hne 3 2 I (linU I) 0 σ (p 1) (p (1/2))
            (hmixjoint 2 2 (a 1) (a (1/2)) c) (hp 1 (Or.inl rfl)) (hp (1/2) (Or.inr rfl))
          intro i d hd
          linarith [hbr 1 (Or.inl rfl) i d hd, hbr (1/2) (Or.inr rfl) i d hd]
        · apply hnotpure 2 2 σ (a 1) (a (1/2))
          · intro h
            have hh := congrFun h 0
            norm_num [a] at hh
          · rfl
      exact ⟨hlinear, hgeneral, hleo⟩
