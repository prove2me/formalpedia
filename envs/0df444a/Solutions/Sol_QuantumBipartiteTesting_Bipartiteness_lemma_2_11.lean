-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_2_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:42:51.801332+00:00
-- url     : https://prove2.me/submissions/d8f6a232-08ec-4600-8efc-7019b0aeebe9

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_matching_mobius_factorization
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_15
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_5
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_9
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private lemma adj_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) : Symmetric (Adj F) := by
  intro u v h
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

private lemma reach_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Relation.ReflTransGen (Adj F) u v) : Relation.ReflTransGen (Adj F) v u := by
  induction h with
  | refl => exact .refl
  | tail h hvw ih => exact (Relation.ReflTransGen.single (adj_symm F hvw)).trans ih

private def reachSetoid {N c : ℕ} (F : Finset (ColoredEdge N c)) : Setoid (Fin N) where
  r := Relation.ReflTransGen (Adj F)
  iseqv := ⟨fun _ => .refl, fun h => reach_symm F h, fun h h' => h.trans h'⟩

private def fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun v => Relation.ReflTransGen (Adj F) u v

private lemma mem_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    v ∈ fullClass F u ↔ Relation.ReflTransGen (Adj F) u v := by
  simp [fullClass]

private lemma self_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) :
    u ∈ fullClass F u := (mem_fullClass F u u).mpr .refl

private lemma fullClass_eq_iff {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    fullClass F u = fullClass F v ↔ Relation.ReflTransGen (Adj F) u v := by
  constructor
  · intro h
    rw [← mem_fullClass F u v, h]
    exact self_fullClass F v
  · intro h
    ext w
    simp only [mem_fullClass]
    exact ⟨fun hw => (reach_symm F h).trans hw, fun hw => h.trans hw⟩

private lemma adj_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Adj F u v) : u ∈ Vertices F ∧ v ∈ Vertices F := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩⟩
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩⟩

private lemma reach_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (hu : u ∈ Vertices F) (h : Relation.ReflTransGen (Adj F) u v) : v ∈ Vertices F := by
  induction h with
  | refl => exact hu
  | @tail v w h hvw ih => exact (adj_incident F hvw).2

private lemma isolated_class {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∉ Vertices F) : fullClass F u = {u} := by
  ext v
  simp only [mem_fullClass, mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail v w h hvw ih => exact (hu (ih ▸ (adj_incident F hvw).1)).elim
  · rintro rfl
    exact .refl

private lemma component_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∈ Vertices F) :
    (Vertices F).filter (fun v => Relation.ReflTransGen (Adj F) u v) = fullClass F u := by
  ext v
  simp only [mem_filter, mem_fullClass]
  exact ⟨And.right, fun h => ⟨reach_incident F hu h, h⟩⟩


private lemma componentAt_eq {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) :
    ComponentAt F i = (Components F).toList[i.val]'(by simpa using i.isLt) := by
  have hi : i.val < (Components F).toList.length := by simpa only [length_toList] using i.isLt
  unfold ComponentAt
  rw [List.getElem?_eq_getElem hi]
  rfl

private lemma componentAt_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : ComponentAt F i ∈ Components F := by
  rw [componentAt_eq]
  exact mem_toList.mp (List.getElem_mem _)

private lemma componentAt_injective {N colors : ℕ} (F : Finset (ColoredEdge N colors)) :
    Function.Injective (ComponentAt F) := by
  intro i j h
  simp only [componentAt_eq] at h
  exact Fin.ext ((Components F).nodup_toList.getElem_inj_iff.mp h)

private lemma componentAt_surjective {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (S : Finset (Fin N)) (hS : S ∈ Components F) : ∃ i, ComponentAt F i = S := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem (mem_toList.mpr hS)
  refine ⟨⟨i,by simpa using hi⟩,?_⟩
  rw [componentAt_eq]
  exact he

private lemma sum_componentAt {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (f : Finset (Fin N) → ℕ) :
    (∑ i : Fin (Components F).card, f (ComponentAt F i)) = ∑ S ∈ Components F, f S := by
  apply Finset.sum_bij (fun i _ => ComponentAt F i)
  · intro i hi; exact componentAt_mem F i
  · intro i hi j hj hij; exact componentAt_injective F hij
  · intro S hS; obtain ⟨i,hi⟩ := componentAt_surjective F S hS; exact ⟨i,mem_univ _,hi⟩
  · intros; rfl

private lemma component_containing {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (u : Fin N) (hu : u ∈ Vertices F) (S : Finset (Fin N)) (hS : S ∈ Components F) :
    u ∈ S ↔ S = fullClass F u := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hS
  rw [component_fullClass F hv,mem_fullClass]
  constructor
  · intro h; exact (fullClass_eq_iff F v u).mpr h
  · intro h; exact (fullClass_eq_iff F v u).mp h

private lemma component_counts {N colors : ℕ} (F : Finset (ColoredEdge N colors)) :
    (∑ i, ∑ j : Fin colors, ComponentColorCount F i j) = F.card := by
  unfold ComponentColorCount
  rw [sum_componentAt F (fun S => ∑ j : Fin colors, (F.filter (fun e => e.1 ∈ S ∧ e.2.2 = j)).card)]
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; intro j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hu : e.1 ∈ Vertices F := by
    simp only [Vertices,mem_filter,mem_univ,true_and]
    exact ⟨e,he,Or.inl rfl⟩
  have hc : fullClass F e.1 ∈ Components F := by
    exact mem_image.mpr ⟨e.1,hu,component_fullClass F hu⟩
  rw [Finset.sum_comm]
  have hh (S : Finset (Fin N)) :
      (∑ j : Fin colors, if e.1 ∈ S ∧ e.2.2 = j then 1 else 0) = if e.1 ∈ S then 1 else 0 := by
    by_cases h : e.1 ∈ S <;> simp [h]
  simp_rw [hh]
  have hi : (∑ S ∈ Components F, if e.1 ∈ S then 1 else 0) =
      ∑ S ∈ Components F, if S = fullClass F e.1 then 1 else 0 := by
    apply sum_congr rfl
    intro S hS
    simp only [component_containing F e.1 hu S hS]
  rw [hi]
  simp [hc]

private lemma topology_factorization {N colors : ℕ} (q : ℕ) (F : Finset (ColoredEdge N colors))
    (he : F.card ≤ 2*q) : ∃ B : Bivariate, B.totalDegree ≤ DenominatorDegree q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        TopologyMoment F M l = l ^ CycleRank F * Eval B M l / Eval (Denominator q) M l := by
  have hd : (∑ i, ∑ j, ComponentColorCount F i j) ≤ 2*q := by
    rw [component_counts]
    exact he
  choose H hdeg hH using (fun p => matching_mobius_factorization (ComponentColorCount F) q hd p)
  refine ⟨∑ p, H p,MvPolynomial.totalDegree_finsetSum_le (fun p hp => hdeg p),?_⟩
  intro M l hl hden
  unfold TopologyMoment
  simp only [PartitionCorrection,PartitionMoment] at hH ⊢
  simp_rw [hH _ M l hl hden,component_counts]
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Eval,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hb : (Blocks p).card ≤ (Components F).card := by
    unfold Blocks
    exact Finset.card_image_le.trans_eq (by simp)
  have heq : (((F.card+(Components F).card-(Blocks p).card:ℕ):ℤ)) =
      (F.card:ℤ)+(Components F).card-(Blocks p).card := by
    omega
  rw [← zpow_natCast,← mul_assoc,← zpow_add₀ hl,heq]
  congr 2
  unfold CycleRank
  ring


private def extendSigns {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : {e // e ∈ F} → Bool) (e : ColoredEdge N c) : Bool :=
  if h : e ∈ F then b ⟨e,h⟩ else false

private lemma rank_nonnegative {N c : ℕ} (F : Finset (ColoredEdge N c)) (hF : Consistent F) :
    0 ≤ CycleRank F := by
  let signs := fun (x : Fin N → Bool) (e : {e // e ∈ F}) => xor (x e.val.1) (x e.val.2.1)
  let base : ℝ := (2 : ℝ)^(-((Vertices F).card : ℤ)+(Components F).card)
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hfiber (b : {e // e ∈ F} → Bool) :
      ((univ.filter (fun x : Fin N → Bool => signs x = b)).card : ℝ) ≤ base * (2 : ℝ)^N := by
    have hset : (univ.filter (fun x : Fin N → Bool => signs x = b)) =
        (univ.filter (fun x : Fin N → Bool => ∀ e ∈ F, xor (x e.1) (x e.2.1) = extendSigns F b e)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hx e he
        have hh := congrFun hx ⟨e,he⟩
        simpa only [signs, extendSigns, dif_pos he] using hh
      · intro hx
        funext e
        simpa only [signs, extendSigns, dif_pos e.property] using hx e.val e.property
    have hp : SignProbYes F (extendSigns F b) ≤ base := by
      rw [(lemma_3_5 F hF (extendSigns F b)).2.1]
      split_ifs
      · exact le_rfl
      · exact hbase
    unfold SignProbYes at hp
    rw [← hset] at hp
    exact (div_le_iff₀ (by positivity)).mp hp
  have hcount : (2 : ℝ)^N ≤ (2 : ℝ)^F.card * (base * (2 : ℝ)^N) := by
    have hc : (univ : Finset (Fin N → Bool)).card =
        ∑ b : {e // e ∈ F} → Bool, (univ.filter (fun x : Fin N → Bool => signs x = b)).card :=
      card_eq_sum_card_fiberwise (fun x _ => mem_univ (signs x))
    have hcr := congrArg (fun n : ℕ => (n : ℝ)) hc
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum] at hcr
    calc
      _ = _ := hcr
      _ ≤ ∑ b : {e // e ∈ F} → Bool, base * (2 : ℝ)^N := sum_le_sum (fun b _ => hfiber b)
      _ = _ := by simp
  have hbound : (1 : ℝ) ≤ (2 : ℝ)^(CycleRank F) := by
    have hm : (1 : ℝ)*(2 : ℝ)^N ≤ ((2 : ℝ)^F.card*base)*(2 : ℝ)^N := by
      nlinarith [hcount]
    have h := (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (2 : ℝ)^N)).mp hm
    have heq : (2 : ℝ)^F.card*base = (2 : ℝ)^(CycleRank F) := by
      dsimp [base]
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      unfold CycleRank
      ring
    rw [heq] at h
    exact h
  exact (one_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hbound

private lemma rank_le_edges {N c : ℕ} (F : Finset (ColoredEdge N c)) : CycleRank F ≤ F.card := by
  have hc : (Components F).card ≤ (Vertices F).card := card_image_le
  unfold CycleRank
  omega

private lemma pattern_card {N colors : ℕ} (T : GraphTable N colors) : (PatternOf T).card ≤ T.val.card := by
  unfold PatternOf
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ az ∈ T.val, 1 := by
      apply sum_le_sum
      intro az haz
      cases az.1.1 <;> simp
    _ = _ := by simp

private def tableExponent {α : Type} [DecidableEq α] (s : Finset α) : α →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

private lemma exponent_support {α : Type} [DecidableEq α] (s : Finset α) :
    (tableExponent s).support = s := by
  ext a
  simp [tableExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]

private lemma exponent_injective {α : Type} [DecidableEq α] :
    Function.Injective (tableExponent (α := α)) := by
  intro s t h
  simpa only [exponent_support] using congrArg Finsupp.support h

private lemma table_monomial {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) :
    TableMonomial T = MvPolynomial.monomial (tableExponent T.val) (1 : ℝ) := by
  simpa only [pow_one, TableMonomial, tableExponent] using
    (MvPolynomial.prod_X_pow (R := ℝ) (fun _ : I × S => 1) T.val)

private lemma canonical_coefficient {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) :
    (CanonicalPolynomial E A out).coeff (tableExponent T.val) = CanonicalCoeff E A out T := by
  unfold CanonicalPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [sum_eq_single T]
  · simp [table_monomial]
  · intro U hU hUT
    have he : tableExponent U.val ≠ tableExponent T.val := by
      intro h
      exact hUT (Subtype.ext (exponent_injective h))
    simp [table_monomial, he]
  · simp

private lemma coefficient_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) (hT : 2*q < T.val.card) :
    CanonicalCoeff E A out T = 0 := by
  have hdegree := (lemma_2_9 E A out).1
  rw [← canonical_coefficient E A out T]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [exponent_support]
  have hsum : (∑ a ∈ T.val, tableExponent T.val a) = T.val.card := by
    simp [tableExponent, Finsupp.indicator_apply]
  rw [hsum]
  exact hdegree.trans_lt hT



private lemma table_numerator {N colors k w q : ℕ}
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing) (T : GraphTable N colors) :
    ∃ H : Bivariate, H.totalDegree ≤ DenominatorDegree q+2*q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        CanonicalCoeff E A out T * FormalMonomial s T M l = Eval H M l / Eval (Denominator q) M l := by
  by_cases hsize : T.val.card ≤ 2*q
  swap
  · refine ⟨0,by simp,?_⟩
    intro M l hl hden
    rw [coefficient_zero E A out T (Nat.lt_of_not_ge hsize)]
    simp [Eval]
  by_cases hcons : ConsistentTable T
  swap
  · refine ⟨0,by simp,?_⟩
    intro M l hl hden
    simp [FormalMonomial,hcons,Eval]
  let F := PatternOf T
  obtain ⟨B,hBdeg,hB⟩ := topology_factorization q F ((pattern_card T).trans hsize)
  have hrank := rank_nonnegative F hcons.1
  let m := (CycleRank F).toNat
  have hm : m ≤ 2*q := by
    have hr := rank_le_edges F
    have he : F.card ≤ 2*q := (pattern_card T).trans hsize
    dsimp only [m]
    omega
  have hr : CycleRank F = (m:ℤ) := (Int.toNat_of_nonneg hrank).symm
  let b := match s with
    | .yes => SignProbYes F (PatternSign T)
    | .no => SignProbNo F (PatternSign T)
  let H : Bivariate := C (CanonicalCoeff E A out T*b)*(X 1^m*B)
  refine ⟨H,?_,?_⟩
  · have hd : H.totalDegree ≤ m+B.totalDegree := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C,zero_add]
      apply (totalDegree_mul _ _).trans_eq
      simp
    omega
  · intro M l hl hden
    have hh := hB M l hl hden
    simp only [FormalMonomial,if_pos hcons]
    change CanonicalCoeff E A out T * (TopologyMoment F M l*b) = _
    rw [hh,hr,zpow_natCast]
    simp only [H,Eval,map_mul,map_pow,eval_C,eval_X,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    ring

private lemma acceptance_numerator {N colors k w q : ℕ}
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing) :
    ∃ H : Bivariate, H.totalDegree ≤ DenominatorDegree q+2*q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        FormalAcceptance E A out s M l = Eval H M l / Eval (Denominator q) M l := by
  choose H hdeg hH using (fun T => table_numerator E A out s T)
  refine ⟨∑ T, H T,MvPolynomial.totalDegree_finsetSum_le (fun T hT => hdeg T),?_⟩
  intro M l hl hden
  unfold FormalAcceptance
  simp_rw [hH _ M l hl hden]
  simp only [Eval,map_sum,Finset.sum_div]

private lemma query_scale_bound (q : ℕ) : (q : ℝ) ≤ 2*DegreeScale q := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hl : (1/2 : ℝ) ≤ Real.log (q+2 : ℝ) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ q+2)
    linarith [Real.log_two_gt_d9]
  unfold DegreeScale
  nlinarith

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N colors q t : ℕ, ∀ A : Fin t → FormalCircuit N colors q, ∀ α : Fin t → ℝ,
      RationalDegreeBound q Cdeg (fun M l => ∑ i, α i * (A i).value M l) := by
  obtain ⟨Cdeg,hC,hbound⟩ := lemma_3_15.1
  refine ⟨Cdeg+4,by linarith,?_⟩
  intro N colors q t A α
  choose H hdeg hH using (fun i => acceptance_numerator (A i).encoding (A i).algorithm (A i).output (A i).signing)
  let P : Bivariate := ∑ i, C (α i)*H i
  refine ⟨P,Denominator q,dvd_refl _,?_,?_⟩
  · have hd : P.totalDegree ≤ DenominatorDegree q+2*q := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i hi
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C,zero_add] using hdeg i
    have hD : DenominatorDegree q ≤ TruncationDegree q := by unfold TruncationDegree; omega
    have hc := hbound q
    have hqd := query_scale_bound q
    have hn : (P.totalDegree:ℝ) ≤ (DenominatorDegree q:ℝ)+2*q := by exact_mod_cast hd
    have hD' : (DenominatorDegree q:ℝ) ≤ TruncationDegree q := by exact_mod_cast hD
    nlinarith
  · intro M l hl hden
    refine ⟨hden,?_⟩
    simp only [FormalCircuit.value]
    simp_rw [hH _ M l hl hden]
    simp only [P,Eval,map_sum,map_mul,eval_C,Finset.sum_div,← mul_div_assoc]
end
