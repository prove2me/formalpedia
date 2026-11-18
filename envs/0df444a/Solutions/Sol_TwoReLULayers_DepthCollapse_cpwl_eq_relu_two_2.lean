-- Prove2me | solution 2 for TwoReLULayers.DepthCollapse.cpwl_eq_relu_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:29:42.431331+00:00
-- url     : https://prove2.me/submissions/32a804e5-51d8-47df-a47c-5a176939f017

import Mathlib
import Definitions.Def_TwoReLULayers_DepthCollapse_Model
import Theorems.Thm_TwoReLULayers_DepthCollapse_max_rational_network
import Theorems.Thm_TwoReLULayers_DepthCollapse_rational_field_extension
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_precomposition
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_linear_combination
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_geometric_cpwl

-- Adapted from kilianar/two-layer-formalization, commit a275280,
-- with rational coefficient preservation and mission evaluator bridges.

-- Source module: Solutions/AffineSelection.lean

namespace AffineSelection
noncomputable section
open Set Filter Topology

 theorem stable_selection {ι : Type*} [Fintype ι] (h : ℝ → ℝ) (g : ι → ℝ → ℝ)
    (hh : Continuous h) (hg : ∀ i, Continuous (g i)) (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ∀ i, h s = g i s → h t = g i t := by
  rw [eventually_all]
  intro i
  by_cases heq : h t = g i t
  · exact Eventually.of_forall fun _ _ => heq
  · exact ((hh.sub (hg i)).continuousAt.eventually_ne (sub_ne_zero.mpr heq)).mono
      fun _ hs heq => (hs (sub_eq_zero.mpr heq)).elim

 theorem crossing {ι : Type*} [Fintype ι] (a b : ι → ℝ) (h : ℝ → ℝ)
    (hh : Continuous h) (h0 : h 0 = 0) (h1 : h 1 = 0)
    (hsel : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, h t = (1-t)*a i + t*b i) :
    ∃ i, 0 ≤ a i ∧ b i ≤ 0 := by
  classical
  by_contra! hno
  let g : ι → ℝ → ℝ := fun i t => (1-t)*a i + t*b i
  have hg : ∀ i, Continuous (g i) := by intro i; dsimp [g]; fun_prop
  have hslope : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, g i t = 0 → 0 < b i - a i := by
    intro t ht i hi
    by_contra! hs
    have hd0 : t * (b i - a i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hs
    have hd1 : (1-t) * (b i - a i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) hs
    have hai : 0 ≤ a i := by dsimp [g] at hi; nlinarith
    have hbi : b i ≤ 0 := by dsimp [g] at hi; nlinarith
    exact (hno i hai).not_ge hbi
  have hsign : ∀ t ∈ Icc (0 : ℝ) 1, h t = 0 →
      ∀ᶠ s in 𝓝 t, s ∈ Icc (0 : ℝ) 1 →
        (s < t → h s < 0) ∧ (t < s → 0 < h s) := by
    intro t ht hzero
    filter_upwards [stable_selection h g hh hg t] with s hs hsc
    obtain ⟨i, hi⟩ := hsel s hsc
    have hit : g i t = 0 := (hs i hi).symm.trans hzero
    have hpos := hslope t ht i hit
    have hid : g i s = (s-t)*(b i-a i) := by dsimp [g] at *; nlinarith [hit]
    rw [hi, show (1-s)*a i+s*b i = g i s from rfl, hid]
    exact ⟨fun hst => mul_neg_of_neg_of_pos (by linarith) hpos,
      fun hts => mul_pos (by linarith) hpos⟩
  have hnear0 := hsign 0 ⟨le_rfl, by norm_num⟩ h0
  have hnear1 := hsign 1 ⟨by norm_num, le_rfl⟩ h1
  obtain ⟨δ0, hδ0, hδ0sign⟩ := Metric.mem_nhds_iff.mp hnear0
  obtain ⟨δ1, hδ1, hδ1sign⟩ := Metric.mem_nhds_iff.mp hnear1
  let u : ℝ := min (min δ0 δ1) (1/4) / 2
  have hu : 0 < u := by dsimp [u]; positivity
  have hu0 : u < δ0 := by dsimp [u]; have := min_le_left δ0 δ1; have := min_le_left (min δ0 δ1) (1/4); linarith
  have hu1 : u < δ1 := by dsimp [u]; have := min_le_right δ0 δ1; have := min_le_left (min δ0 δ1) (1/4); linarith
  have hu4 : u < 1/4 := by dsimp [u]; have := min_le_right (min δ0 δ1) (1/4); linarith
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu.le, by linarith⟩
  have hvI : 1-u ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hupos : 0 < h u := (hδ0sign (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hu] using hu0) huI).2 hu
  have hvneg : h (1-u) < 0 := (hδ1sign (by
    simp only [Metric.mem_ball, Real.dist_eq]
    rw [show 1-u-1 = -u by ring, abs_neg, abs_of_pos hu]
    exact hu1) hvI).1 (by linarith)
  let Z : Set ℝ := Icc u (1-u) ∩ h ⁻¹' {0}
  have hZcomp : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hh)
  have hZne : Z.Nonempty := by
    obtain ⟨z, hz, heq⟩ := intermediate_value_Icc' (show u ≤ 1-u by linarith) hh.continuousOn
      (show (0 : ℝ) ∈ Icc (h (1-u)) (h u) from ⟨hvneg.le, hupos.le⟩)
    exact ⟨z, hz, heq⟩
  obtain ⟨z, hz, hzmin⟩ := hZcomp.exists_isLeast hZne
  have hzu : u < z := lt_of_le_of_ne hz.1.1 (by intro heq; have := hz.2; simpa [← heq, hupos.ne'] using this)
  have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  obtain ⟨δ, hδ, hδsign⟩ := Metric.mem_nhds_iff.mp (hsign z hzI hz.2)
  let v := z - min δ (z-u) / 2
  have huv : u < v := by dsimp [v]; have := min_le_right δ (z-u); linarith
  have hvz : v < z := by dsimp [v]; have : 0 < min δ (z-u) := lt_min hδ (by linarith); linarith
  have hvball : v ∈ Metric.ball z δ := by
    simp only [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hvz)]
    dsimp [v]
    have := min_le_left δ (z-u)
    linarith
  have hvnegative : h v < 0 := (hδsign hvball ⟨by linarith, by linarith [hzI.2]⟩).1 hvz
  obtain ⟨w, hw, hwzero⟩ := intermediate_value_Icc' (show u ≤ v by linarith) hh.continuousOn
    (show (0 : ℝ) ∈ Icc (h v) (h u) from ⟨hvnegative.le, hupos.le⟩)
  have hzw : z ≤ w := hzmin ⟨⟨hw.1, by linarith [hw.2, hz.1.2]⟩, hwzero⟩
  linarith [hw.2]

end
end AffineSelection

-- Source module: Solutions/DCRepresentation.lean

namespace TwoReLULayers.DepthCollapse
noncomputable section
open Finset

 def affineZero {R : Subfield ℝ} {n : ℕ} : AffineScalar R n := ⟨fun _ => 0, 0⟩
 def affineAdd {R : Subfield ℝ} {n : ℕ} (a b : AffineScalar R n) : AffineScalar R n :=
  ⟨fun i => a.weight i + b.weight i, a.bias + b.bias⟩
 @[simp] theorem affineZero_eval {R : Subfield ℝ} {n : ℕ} (x : E n) :
    (affineZero : AffineScalar R n).eval x = 0 := by simp [affineZero, AffineScalar.eval]
 @[simp] theorem affineAdd_eval {R : Subfield ℝ} {n : ℕ} (a b : AffineScalar R n) (x : E n) :
    (affineAdd a b).eval x = a.eval x + b.eval x := by
  simp [affineAdd, AffineScalar.eval, add_mul, sum_add_distrib]
  ring

 def affineMax {R : Subfield ℝ} {n : ℕ} (S : Finset (AffineScalar R n)) (hS : S.Nonempty) :
    E n → ℝ := fun x => S.sup' hS (fun a => a.eval x)

 def DC {n : ℕ} (R : Subfield ℝ) (f : E n → ℝ) : Prop :=
  ∃ S T : Finset (AffineScalar R n), ∃ hS : S.Nonempty, ∃ hT : T.Nonempty,
    ∀ x, f x = affineMax S hS x - affineMax T hT x

 theorem dc_affine {n : ℕ} (R : Subfield ℝ) (a : AffineScalar R n) : DC R a.eval := by
  classical
  exact ⟨{a}, {affineZero}, singleton_nonempty _, singleton_nonempty _, by simp [affineMax]⟩

 theorem dc_neg {n : ℕ} (R : Subfield ℝ) {f : E n → ℝ} (hf : DC R f) :
    DC R (fun x => -f x) := by
  obtain ⟨S, T, hS, hT, hf⟩ := hf
  exact ⟨T, S, hT, hS, fun x => by change -f x = _; rw [hf]; ring⟩

 theorem affineMax_sum {n : ℕ} {R : Subfield ℝ} (S T : Finset (AffineScalar R n))
    (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ U : Finset (AffineScalar R n), ∃ hU : U.Nonempty,
      ∀ x, affineMax U hU x = affineMax S hS x + affineMax T hT x := by
  classical
  let U := (S ×ˢ T).image (fun ab => affineAdd ab.1 ab.2)
  have hU : U.Nonempty := (hS.product hT).image _
  refine ⟨U, hU, fun x => ?_⟩
  apply le_antisymm
  · apply sup'_le
    intro a ha
    obtain ⟨⟨s,t⟩, hst, rfl⟩ := mem_image.mp ha
    rw [affineAdd_eval]
    exact add_le_add (le_sup' (fun a => a.eval x) (mem_product.mp hst).1)
      (le_sup' (fun a => a.eval x) (mem_product.mp hst).2)
  · obtain ⟨a, ha, heqa⟩ := exists_mem_eq_sup' hS (fun a => a.eval x)
    obtain ⟨b, hb, heqb⟩ := exists_mem_eq_sup' hT (fun a => a.eval x)
    change S.sup' hS _ + T.sup' hT _ ≤ U.sup' hU _
    rw [heqa, heqb]
    exact (affineAdd_eval a b x).symm ▸
      (le_sup' (fun a : AffineScalar R n => a.eval x)
        (show affineAdd a b ∈ U from mem_image.mpr ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, rfl⟩))

 theorem dc_max {n : ℕ} (R : Subfield ℝ) {f g : E n → ℝ} (hf : DC R f) (hg : DC R g) :
    DC R (fun x => max (f x) (g x)) := by
  classical
  obtain ⟨S, T, hS, hT, hf⟩ := hf
  obtain ⟨U, V, hU, hV, hg⟩ := hg
  obtain ⟨A, hA, hAval⟩ := affineMax_sum S V hS hV
  obtain ⟨B, hB, hBval⟩ := affineMax_sum U T hU hT
  obtain ⟨C, hC, hCval⟩ := affineMax_sum T V hT hV
  refine ⟨A ∪ B, C, hA.mono subset_union_left, hC, fun x => ?_⟩
  have hmax : affineMax (A ∪ B) (hA.mono subset_union_left) x =
      max (affineMax A hA x) (affineMax B hB x) := by
    exact sup'_union hA hB _
  change max (f x) (g x) = _
  rw [hmax, hAval, hBval, hCval, hf, hg]
  rw [← max_sub_sub_right]
  congr 1 <;> ring

 theorem dc_min {n : ℕ} (R : Subfield ℝ) {f g : E n → ℝ} (hf : DC R f) (hg : DC R g) :
    DC R (fun x => min (f x) (g x)) := by
  have h := dc_neg R (dc_max R (dc_neg R hf) (dc_neg R hg))
  have heq : (fun x => -max (-f x) (-g x)) = (fun x => min (f x) (g x)) := by
    ext x
    by_cases hfg : f x ≤ g x
    · rw [max_eq_left (neg_le_neg hfg), min_eq_left hfg, neg_neg]
    · rw [max_eq_right (neg_le_neg (le_of_not_ge hfg)), min_eq_right (le_of_not_ge hfg), neg_neg]
  rwa [heq] at h

 theorem dc_finset_sup {n : ℕ} {ι : Type*} (R : Subfield ℝ) (S : Finset ι) (hS : S.Nonempty)
    (f : ι → E n → ℝ) (hf : ∀ i ∈ S, DC R (f i)) :
    DC R (fun x => S.sup' hS (fun i => f i x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS
  | insert i S hi ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · simpa using hf i (mem_insert_self _ _)
    · have h := dc_max R (hf i (mem_insert_self _ _))
        (ih hSne (fun j hj => hf j (mem_insert_of_mem hj)))
      simpa only [sup'_insert hSne] using h

 theorem dc_finset_inf {n : ℕ} {ι : Type*} (R : Subfield ℝ) (S : Finset ι) (hS : S.Nonempty)
    (f : ι → E n → ℝ) (hf : ∀ i ∈ S, DC R (f i)) :
    DC R (fun x => S.inf' hS (fun i => f i x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS
  | insert i S hi ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · simpa using hf i (mem_insert_self _ _)
    · have h := dc_min R (hf i (mem_insert_self _ _))
        (ih hSne (fun j hj => hf j (mem_insert_of_mem hj)))
      simpa only [inf'_insert hSne] using h

end
end TwoReLULayers.DepthCollapse

-- Source module: Solutions/GeometricDC.lean

namespace TwoReLULayers.DepthCollapse
noncomputable section
open Finset

 theorem affine_segment {n : ℕ} {R : Subfield ℝ} (a : AffineScalar R n) (x y : E n) (t : ℝ) :
    a.eval ((1-t) • x + t • y) = (1-t)*a.eval x + t*a.eval y := by
  change (a.bias : ℝ) + ∑ i, (a.weight i : ℝ)*((1-t)*x i+t*y i) = _
  calc
    (a.bias : ℝ) + ∑ i, (a.weight i : ℝ)*((1-t)*x i+t*y i) =
        (a.bias : ℝ) + ((1-t)*(∑ i, (a.weight i : ℝ)*x i) +
          t*(∑ i, (a.weight i : ℝ)*y i)) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by unfold AffineScalar.eval; ring


 theorem selection_crossing {n k : ℕ} {R : Subfield ℝ} (f : E n → ℝ)
    (hf : Continuous f) (a : Fin k → AffineScalar R n)
    (hsel : ∀ x, ∃ i, f x = (a i).eval x) (x y : E n) :
    ∃ i, f x ≤ (a i).eval x ∧ (a i).eval y ≤ f y := by
  let h : ℝ → ℝ := fun t => f ((1-t) • x + t • y) - ((1-t)*f x+t*f y)
  have hcont : Continuous h := by
    apply Continuous.sub
    · apply hf.comp
      fun_prop
    · fun_prop
  obtain ⟨i, hi0, hi1⟩ := AffineSelection.crossing
    (fun i => (a i).eval x - f x) (fun i => (a i).eval y - f y) h hcont
    (by simp [h]) (by simp [h]) (by
      intro t ht
      obtain ⟨i, hi⟩ := hsel ((1-t) • x+t • y)
      refine ⟨i, ?_⟩
      dsimp [h]
      rw [hi, affine_segment]
      ring)
  exact ⟨i, by linarith, by linarith⟩

 theorem continuous_selection_dc {n k : ℕ} (R : Subfield ℝ) (f : E n → ℝ)
    (hf : Continuous f) (a : Fin k → AffineScalar R n)
    (hsel : ∀ x, ∃ i, f x = (a i).eval x) : DC R f := by
  classical
  let S : E n → Finset (Fin k) := fun x => univ.filter (fun i => f x ≤ (a i).eval x)
  have hSne : ∀ x, (S x).Nonempty := by
    intro x
    obtain ⟨i, hi⟩ := hsel x
    exact ⟨i, by simp [S, hi]⟩
  let J := {T : Finset (Fin k) // ∃ x : E n, T = S x}
  letI : Fintype J := Fintype.ofFinite J
  letI : Nonempty J := ⟨⟨S 0, 0, rfl⟩⟩
  have hJne : ∀ j : J, j.val.Nonempty := by
    rintro ⟨T, x, rfl⟩
    exact hSne x
  let F : J → E n → ℝ := fun j x => j.val.inf' (hJne j) (fun i => (a i).eval x)
  have hlow : ∀ j : J, ∀ x, F j x ≤ f x := by
    rintro ⟨T, y, rfl⟩ x
    obtain ⟨i, hiy, hix⟩ := selection_crossing f hf a hsel y x
    exact (inf'_le (fun i => (a i).eval x) (by simp [S, hiy])).trans hix
  have heq : f = fun x => (univ : Finset J).sup' univ_nonempty (fun j => F j x) := by
    ext x
    apply le_antisymm
    · refine le_sup'_of_le _ (mem_univ (⟨S x, x, rfl⟩ : J)) ?_
      apply le_inf'
      intro i hi
      exact (mem_filter.mp hi).2
    · exact sup'_le _ _ fun j _ => hlow j x
  rw [heq]
  apply dc_finset_sup R univ univ_nonempty F
  intro j hj
  exact dc_finset_inf R j.val (hJne j) (fun i => (a i).eval) (fun i hi => dc_affine R (a i))

 theorem geometric_cpwl_dc {n : ℕ} (R : Subfield ℝ) (f : E n → ℝ)
    (hf : f ∈ CPWL R n) : DC R f := by
  obtain ⟨hcont, k, P, a, hP, hcover, heq⟩ := hf
  apply continuous_selection_dc R f hcont a
  intro x
  obtain ⟨j, hj⟩ := hcover x
  exact ⟨j, heq j x hj⟩

end
end TwoReLULayers.DepthCollapse

-- Source module: Solutions/CompleteDepthCollapse.lean

namespace TwoReLULayers.DepthCollapse
noncomputable section
open Finset

 theorem finite_affineMax_network {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (S : Finset (AffineScalar R n)) (hS : S.Nonempty) : affineMax S hS ∈ ReLU2 R n := by
  classical
  let A : AffineR R n S.card := fun i => (S.equivFin.symm i).val
  have hcard : 1 ≤ S.card := hS.card_pos
  have hmax := rational_field_extension hcard R (maxCoord : E S.card → ℝ)
    (max_rational_network hcard)
  have hpre := network_precomposition hn hcard R A maxCoord hmax
  have heq : affineMax S hS = fun x => maxCoord (affineEval A x) := by
    ext x
    apply le_antisymm
    · apply sup'_le
      intro a ha
      apply le_csSup (Set.finite_range (fun i : Fin S.card => (A i).eval x)).bddAbove
      exact ⟨S.equivFin ⟨a,ha⟩, by simp [A, affineEval]⟩
    · apply csSup_le
      · exact ⟨_, ⟨⟨0, hS.card_pos⟩, rfl⟩⟩
      · rintro _ ⟨i, rfl⟩
        exact le_sup' (fun a => a.eval x) (S.equivFin.symm i).property
  rw [heq]
  exact hpre

 theorem dc_network {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ) (f : E n → ℝ)
    (hf : DC R f) : f ∈ ReLU2 R n := by
  obtain ⟨S, T, hS, hT, hf⟩ := hf
  have h := network_linear_combination hn R (![1,-1] : Fin 2 → R)
    (![affineMax S hS, affineMax T hT])
    (by
      intro i
      fin_cases i
      · exact finite_affineMax_network hn R S hS
      · exact finite_affineMax_network hn R T hT)
  have heq : f = fun x => ∑ i : Fin 2,
      (((![1,-1] : Fin 2 → R) i) : ℝ) * (![affineMax S hS, affineMax T hT] i) x := by
    ext x
    simpa [Fin.sum_univ_two, sub_eq_add_neg] using hf x
  rw [heq]
  exact h

end
end TwoReLULayers.DepthCollapse

open TwoReLULayers.DepthCollapse

theorem solution {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ) :
    CPWL R n = ReLU2 R n := by
  apply Set.Subset.antisymm
  · intro f hf
    exact dc_network hn R f (geometric_cpwl_dc R f hf)
  · rintro f ⟨N, hN⟩
    have heq : f = N.eval := funext hN
    rw [heq]
    exact network_geometric_cpwl hn R N
