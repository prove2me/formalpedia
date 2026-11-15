-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:47:20.099121+00:00
-- url     : https://prove2.me/submissions/a3e9e359-6bce-4541-bfe6-a955fc505762

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_2

set_option autoImplicit false

-- Solutions.StratifyMarketsBernoulli
section
open MeasureTheory Set ProbabilityTheory

namespace StratifyMarkets.Bernoulli

/-- The amount above an integer threshold for a sum of independent Bernoulli
trials. Deleting the successful trial bounds the excess beyond the first unit. -/
theorem stop_loss {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (Y : Fin r → Ω → ℝ) (hm : ∀ j, Measurable (Y j))
    (hb : ∀ j, ∀ᵐ x ∂P, Y j x = 0 ∨ Y j x = 1) (hi : iIndepFun Y P) (k : ℕ) :
    (∫ x, max ((∑ j, Y j x) - (k:ℝ)) 0 ∂P) ≤
      (1+∫ x, ∑ j, Y j x ∂P) * P.real {x | (k:ℝ)+1 ≤ ∑ j, Y j x} := by
  classical
  let N := fun x => ∑ j, Y j x
  let E := {x | (k:ℝ)+1 ≤ N x}
  let rest := fun (j : Fin r) x => ∑ i ∈ Finset.univ.erase j, Y i x
  let A := fun j => {x | (k:ℝ)+1 ≤ rest j x}
  have nm : Measurable N := Finset.measurable_sum _ (fun j _ => hm j)
  have rm (j) : Measurable (rest j) := Finset.measurable_sum _ (fun i _ => hm i)
  have em : MeasurableSet E := measurableSet_le measurable_const nm
  have am (j) : MeasurableSet (A j) := measurableSet_le measurable_const (rm j)
  have yi (j) : Integrable (Y j) P := by
    apply Integrable.of_bound (hm j).aestronglyMeasurable 1
    filter_upwards [hb j] with x h
    rcases h with h|h <;> simp [h]
  have ni : Integrable N P := integrable_finsetSum _ (fun j _ => yi j)
  have pi : Integrable (fun x => max (N x-(k:ℝ)) 0) P := (ni.sub (integrable_const _)).sup (integrable_zero _ _ _)
  have part (j) : Integrable ((A j).indicator (Y j)) P := (yi j).indicator (am j)
  have base : Integrable (E.indicator (fun _ => (1:ℝ))) P := (integrable_const _).indicator em
  have pt : ∀ᵐ x ∂P, max (N x - (k:ℝ)) 0 ≤ E.indicator (fun _ => (1:ℝ)) x + ∑ j, (A j).indicator (Y j) x := by
    filter_upwards [ae_all_iff.mpr hb] with x hx
    have int : N x = ((Finset.univ.filter (fun j => Y j x = 1)).card : ℝ) := by
      have coord (j) : Y j x = if Y j x = 1 then (1:ℝ) else 0 := by rcases hx j with H|H <;> simp [H]
      calc _ = ∑ j, if Y j x = 1 then (1:ℝ) else 0 := Finset.sum_congr rfl (fun j _ => coord j)
           _ = _ := Finset.sum_boole _ _
    have re (j) : rest j x + Y j x = N x := Finset.sum_erase_add _ _ (Finset.mem_univ j)
    have n0 (j) : 0 ≤ Y j x := by rcases hx j with H|H <;> simp [H]
    have pos : 0 ≤ ∑ j, (A j).indicator (Y j) x := Finset.sum_nonneg fun j _ => by
      by_cases H : x ∈ A j <;> simp [H,n0 j]
    by_cases high : (k:ℝ)+2 ≤ N x
    · have hit : x ∈ E := by change (k:ℝ)+1 ≤ N x; linarith
      have all (j) : x ∈ A j := by
        change (k:ℝ)+1 ≤ rest j x
        rcases hx j with H|H <;> linarith only [high,re j,H]
      simp only [Set.indicator_of_mem hit,Set.indicator_of_mem (all _)]
      change max (N x - (k:ℝ)) 0 ≤ 1 + N x
      rw [max_eq_left (by linarith)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    · by_cases hit : x ∈ E
      · change (k:ℝ)+1 ≤ N x at hit
        have cut : N x ≤ (k:ℝ)+1 := by
          rw [int] at high ⊢
          norm_cast at high
          exact_mod_cast (by omega : (Finset.univ.filter (fun j => Y j x = 1)).card ≤ k+1)
        rw [Set.indicator_of_mem (show x ∈ E from hit)]
        exact max_le (by linarith) (by linarith)
      · change ¬(k:ℝ)+1 ≤ N x at hit
        have cut : N x ≤ (k:ℝ) := by
          rw [int] at hit ⊢
          norm_cast at hit
          exact_mod_cast (by omega : (Finset.univ.filter (fun j => Y j x = 1)).card ≤ k)
        rw [max_eq_right (sub_nonpos.mpr cut),Set.indicator_of_notMem (show x ∉ E from hit),zero_add]
        exact pos
  have mon := integral_mono_ae pi (base.add (integrable_finsetSum _ (fun j _ => part j))) pt
  simp only [Pi.add_apply] at mon
  rw [integral_add base (integrable_finsetSum _ (fun j _ => part j)),integral_finsetSum _ (fun j _ => part j),
    integral_indicator em,setIntegral_one_eq_measureReal] at mon
  have each (j) : (∫ x, (A j).indicator (Y j) x ∂P) ≤ (∫ x, Y j x ∂P)*P.real E := by
    have ind : IndepFun (rest j) (Y j) P := by
      apply (hi.indepFun_finsetSum_of_notMem hm (Finset.notMem_erase j Finset.univ)).congr _ (Filter.EventuallyEq.rfl)
      exact Filter.Eventually.of_forall (fun x => Finset.sum_apply x (Finset.univ.erase j) Y)
    have eq (x) : (A j).indicator (Y j) x =
      (Ici ((k:ℝ)+1)).indicator (fun _ => (1:ℝ)) (rest j x) * id (Y j x) := by
      by_cases H : (k:ℝ)+1 ≤ rest j x <;> simp [A,Set.indicator,H]
    simp_rw [eq]
    rw [ind.integral_fun_comp_mul_comp (rm j).aemeasurable (hm j).aemeasurable
      (measurable_const.indicator measurableSet_Ici).aestronglyMeasurable measurable_id.aestronglyMeasurable]
    have fun_eq : (fun x => (Ici ((k:ℝ)+1)).indicator (fun _ => (1:ℝ)) (rest j x)) = (A j).indicator (fun _ => (1:ℝ)) := rfl
    rw [fun_eq,integral_indicator (am j),setIntegral_one_eq_measureReal,mul_comm]
    have sub : A j ≤ᵐ[P] E := by
      filter_upwards [hb j] with x hx mem
      have re : rest j x + Y j x = N x := Finset.sum_erase_add _ _ (Finset.mem_univ j)
      change (k:ℝ)+1 ≤ rest j x at mem
      change (k:ℝ)+1 ≤ N x
      rcases hx with H|H <;> linarith
    have le : P.real (A j) ≤ P.real E := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae sub)
    exact mul_le_mul_of_nonneg_left le (integral_nonneg_of_ae ((hb j).mono fun x hx => by rcases hx with H|H <;> simp [H]))
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
  rw [← Finset.sum_mul, ← integral_finsetSum _ (fun j _ => yi j)] at sum
  change _ ≤ (1+∫ x, N x ∂P)*P.real E
  rw [add_mul,one_mul]
  linarith only [mon,sum]

end StratifyMarkets.Bernoulli
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_8
section
open MeasureTheory Set ProbabilityTheory StratifyMarkets.DoubleAuction StratifyMarkets.Bernoulli

private theorem nat_values {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    ∀ᵐ ω ∂P, ∃ k ≤ n, (∑ i, X i ω) = (k:ℝ) := by
  classical
  filter_upwards [ae_all_iff.mpr hb] with ω h
  let s := Finset.univ.filter (fun i => X i ω = 1)
  refine ⟨s.card,by simpa using Finset.card_le_univ s,?_⟩
  have co (i) : X i ω = if X i ω = 1 then (1:ℝ) else 0 := by rcases h i with H|H <;> simp [H]
  calc _ = ∑ i, if X i ω = 1 then (1:ℝ) else 0 := Finset.sum_congr rfl fun i _ => co i
       _ = _ := Finset.sum_boole _ _

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l r : ℕ) (X : Fin l → Ω → ℝ) (Y : Fin r → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hYb : ∀ j, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXY : IndepFun (fun ω => ∑ i, X i ω) (fun ω => ∑ j, Y j ω) P)
    (hmean : ∫ ω, ∑ i, X i ω ∂P ≤ ∫ ω, ∑ j, Y j ω ∂P) (hfour : ∫ ω, ∑ j, Y j ω ∂P < 4) :
    (1/7:ENNReal) * P {ω | 5 < max (1 + ∑ i, X i ω) (∑ j, Y j ω)} ≤
      P {ω | 1 + ∑ i, X i ω ≤ ∑ j, Y j ω} := by
  classical
  let A := fun ω => ∑ i, X i ω
  let B := fun ω => ∑ j, Y j ω
  let D := {ω | 1 + A ω ≤ B ω}
  let H := {ω | 5 < max (1+A ω) (B ω)}
  let E := {ω | 4 < B ω}
  let F := {ω | B ω ≤ 4 ∧ 4 < A ω}
  have aM : Measurable A := Finset.measurable_sum _ fun i _ => hXm i
  have bM : Measurable B := Finset.measurable_sum _ fun j _ => hYm j
  have dM : MeasurableSet D := measurableSet_le (measurable_const.add aM) bM
  have fM : MeasurableSet F := (measurableSet_le bM measurable_const).inter (measurableSet_lt measurable_const aM)
  have ea : ∀ᵐ ω ∂P, ∃ k ≤ l, A ω = (k:ℝ) := nat_values P X hXb
  have eb : ∀ᵐ ω ∂P, ∃ k ≤ r, B ω = (k:ℝ) := nat_values P Y hYb
  have ma {s t : Set Ω} (h : s ≤ᵐ[P] t) : P.real s ≤ P.real t :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)
  have int {n : ℕ} (V : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (V i)) (hb : ∀ i, ∀ᵐ x ∂P, V i x=0 ∨ V i x=1) :
      Integrable (fun x => ∑ i, V i x) P := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.of_bound (hm i).aestronglyMeasurable 1
    filter_upwards [hb i] with x h
    rcases h with h|h <;> simp [h]
  have iA : Integrable A P := int X hXm hXb
  have iB : Integrable B P := int Y hYm hYb
  have partition : P.real H ≤ P.real E + P.real F := by
    have sub : H ⊆ E ∪ F := by
      intro ω h
      change 5 < max (1 + A ω) (B ω) at h
      rcases lt_max_iff.mp h with h|h
      · by_cases e : 4 < B ω
        · exact Or.inl e
        · exact Or.inr ⟨le_of_not_gt e,by change 4 < A ω; linarith only [h]⟩
      · exact Or.inl (by change 4 < B ω; linarith only [h])
    exact (measureReal_mono sub).trans (measureReal_union_le E F)
  have largeB : P.real E ≤ 2 * P.real D := by
    let C := A ⁻¹' Iio 5
    have half := ENNReal.toReal_mono (measure_ne_top _ _) (theorem_4_2 P l X hXm hXb hXi).2.2
    norm_num at half
    have sub : {x | A x < (∫ y, A y ∂P) + 1} ⊆ C := by
      intro x hx; change A x < _ at hx; change A x < 5
      linarith only [hx,hmean.trans_lt hfour]
    have hC : (1/2:ℝ) ≤ P.real C := half.trans (measureReal_mono sub)
    have rect := hXY.measure_inter_preimage_eq_mul (Iio 5) (Ioi 4) measurableSet_Iio measurableSet_Ioi
    have product : P.real (C ∩ E) = P.real C * P.real E := by
      change (P ((A ⁻¹' Iio 5) ∩ (B ⁻¹' Ioi 4))).toReal = _
      rw [rect,ENNReal.toReal_mul]; rfl
    have hit : (C ∩ E : Set Ω) ≤ᵐ[P] D := by
      filter_upwards [ea,eb] with x ⟨j,_,aj⟩ ⟨k,_,bk⟩ ⟨hc,he⟩
      change A x < 5 at hc; change 4 < B x at he; change 1+A x ≤ B x
      rw [aj] at hc; rw [bk] at he; rw [aj,bk]
      norm_cast at hc he ⊢
      omega
    have W := ma hit
    rw [product] at W
    linarith only [W,mul_le_mul_of_nonneg_right hC (measureReal_nonneg (μ := P) (s := E))]
  have excess : P.real F ≤ (∫ x, max (B x - A x) 0 ∂P) := by
    have R : Integrable (fun x => max (A x-B x) 0) P := (iA.sub iB).sup (integrable_zero _ _ _)
    have S : Integrable (fun x => max (B x-A x) 0) P := (iB.sub iA).sup (integrable_zero _ _ _)
    have bound : F.indicator (fun _ => (1:ℝ)) ≤ᵐ[P] fun x => max (A x - B x) 0 := by
      filter_upwards [ea,eb] with x ⟨j,_,aj⟩ ⟨k,_,bk⟩
      by_cases h : x ∈ F
      · rw [Set.indicator_of_mem h]
        have H := h.1
        have K := h.2
        change B x ≤ 4 at H; change 4 < A x at K
        rw [bk] at H; rw [aj] at K
        rw [aj,bk]
        apply le_trans _ (le_max_left _ _)
        norm_cast at H K
        have L : k+1 ≤ j := by omega
        linarith only [show (k:ℝ)+1 ≤ j by exact_mod_cast L] 
      · rw [Set.indicator_of_notMem h]; exact le_max_right _ _
    have ht := integral_mono_ae ((integrable_const _).indicator fM) R bound
    rw [integral_indicator fM,setIntegral_one_eq_measureReal] at ht
    have sub : (∫ x, max (A x-B x) 0 ∂P) - (∫ x, max (B x-A x) 0 ∂P) = (∫ x, A x ∂P) - ∫ x, B x ∂P := by
      rw [← integral_sub R S, ← integral_sub iA iB]
      apply integral_congr_ae
      filter_upwards with x
      by_cases q : A x ≤ B x
      · rw [max_eq_right (sub_nonpos.mpr q),max_eq_left (sub_nonneg.mpr q)]; ring
      · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge q)),max_eq_right (sub_nonpos.mpr (le_of_not_ge q))]; ring
    linarith only [sub,ht,hmean]
  let T := Finset.range (l+1)
  let mass := fun k : ℕ => A ⁻¹' {(k:ℝ)}
  let J := fun k : ℕ => Ici ((k:ℝ)+1)
  let gain := fun (k : ℕ) (y : ℝ) => max (y-k) 0
  let term := fun (k : ℕ) (x : Ω) => (mass k).indicator (fun z => gain k (B z)) x
  let success := fun (k : ℕ) (x : Ω) => (mass k).indicator (fun z => (J k).indicator (fun _ => (1:ℝ)) (B z)) x
  have integ (k) : Integrable (term k) P :=
    ((iB.sub (integrable_const (k:ℝ))).sup (integrable_zero _ _ _)).indicator (aM (measurableSet_singleton _))
  have iwin (k) : Integrable (success k) P := ((integrable_const (1:ℝ)).indicator (bM measurableSet_Ici)).indicator (aM (measurableSet_singleton _))
  have sliced (u : ℕ → ℝ → ℝ) (x : Ω) {j : ℕ} (hj : j ≤ l) (aj : A x = (j:ℝ)) :
      (∑ k ∈ T, (mass k).indicator (fun z => u k (B z)) x) = u j (B x) := by
    rw [Finset.sum_eq_single j,Set.indicator_of_mem (show x ∈ mass j from aj)]
    · intro i _ ne
      apply Set.indicator_of_notMem
      intro e
      exact ne (by exact_mod_cast ((show A x = (i:ℝ) from e).symm.trans aj))
    · simp [T,hj]
  have fact (k : ℕ) (u : ℝ → ℝ) (hu : Measurable u) :
      (∫ x, (mass k).indicator (fun z => u (B z)) x ∂P) = P.real (mass k) * ∫ x, u (B x) ∂P := by
    let v := ({(k:ℝ)} : Set ℝ).indicator (fun _ => (1:ℝ))
    have ev (x) : (mass k).indicator (fun z => u (B z)) x = v (A x)*u (B x) := by
      by_cases h : A x = (k:ℝ) <;> simp [mass,v,Set.indicator,h]
    simp_rw [ev]
    rw [hXY.integral_fun_comp_mul_comp aM.aemeasurable bM.aemeasurable
      (measurable_const.indicator (measurableSet_singleton _)).aestronglyMeasurable hu.aestronglyMeasurable]
    have eq : (fun x => v (A x)) = (mass k).indicator (fun _ => (1:ℝ)) := rfl
    rw [eq,integral_indicator (aM (measurableSet_singleton _)),setIntegral_one_eq_measureReal]
  have stop (k) : ∫ x, term k x ∂P ≤ (1+∫ x, B x ∂P) * ∫ x, success k x ∂P := by
    dsimp only [term,success]
    rw [fact k (gain k) (by dsimp [gain]; fun_prop),fact k _ (measurable_const.indicator measurableSet_Ici)]
    have eq : (fun x => (J k).indicator (fun _ => (1:ℝ)) (B x)) = (B ⁻¹' J k).indicator (fun _ => (1:ℝ)) := rfl
    rw [eq,integral_indicator (bM measurableSet_Ici),setIntegral_one_eq_measureReal]
    have H := mul_le_mul_of_nonneg_left (stop_loss P Y hYm hYb hYi k) (measureReal_nonneg (μ := P) (s := mass k))
    change _ ≤ (1+∫ x, B x ∂P)*(P.real (mass k)*P.real (B ⁻¹' J k))
    rw [mul_left_comm]
    exact H
  have vals : (∫ x, max (B x-A x) 0 ∂P) = ∑ k ∈ T, ∫ x, term k x ∂P := by
    rw [← integral_finsetSum _ (fun i _ => integ i)]
    apply integral_congr_ae
    filter_upwards [ea] with x ⟨j,hj,aj⟩
    rw [aj]
    exact (sliced gain x hj aj).symm
  have wins : P.real D = ∑ k ∈ T, ∫ x, success k x ∂P := by
    rw [← integral_finsetSum _ (fun i _ => iwin i),← setIntegral_one_eq_measureReal,← integral_indicator dM]
    apply integral_congr_ae
    filter_upwards [ea] with x ⟨j,hj,aj⟩
    have H := sliced (fun k => (J k).indicator (fun _ => (1:ℝ))) x hj aj
    change D.indicator (fun _ => (1:ℝ)) x = _
    rw [H]
    by_cases h : 1+A x ≤ B x <;> simp [D,J,Set.indicator,aj,add_comm] at h ⊢ <;> simp [h]
  have sum := Finset.sum_le_sum (s := T) fun k _ => stop k
  rw [← Finset.mul_sum,← vals,← wins] at sum
  have total : 1/7*P.real H ≤ P.real D := by
    linarith only [partition,largeB,excess,sum,mul_le_mul_of_nonneg_right (show 1+(∫ x, B x ∂P) ≤ 5 by linarith only [hfour]) (measureReal_nonneg (μ := P) (s := D))]
  apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _)).mp
  simpa only [H,D,A,B,measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using total
end
