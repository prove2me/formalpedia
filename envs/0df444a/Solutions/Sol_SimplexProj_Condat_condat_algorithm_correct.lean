-- Prove2me | solution 1 for SimplexProj.Condat.condat_algorithm_correct
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T04:08:40.899194+00:00
-- url     : https://prove2.me/submissions/ddfa3490-3810-49e8-994d-1f0f9d243267

import Init
import Definitions.Def_SimplexProj_Condat_condatAlgorithm
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

open SimplexProj.Condat
namespace CondatRemoval
lemma threshold_mono (ys : List ℝ) (c : ℕ) (ρ : ℝ) :
    ρ ≤ (removalPass ys c ρ).2 := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass]
    split_ifs with h
    · exact (le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg _))).trans (ih _ _)
    · exact ih _ _
lemma sublist (ys : List ℝ) (c : ℕ) (ρ : ℝ) :
    (removalPass ys c ρ).1.Sublist ys := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass]
    split_ifs
    · exact (ih _ _).cons _
    · exact (ih _ _).cons_cons _
lemma hinge_sum (ys : List ℝ) (c : ℕ) (ρ : ℝ) :
    (ys.map (fun y => max (y-(removalPass ys c ρ).2) 0)).sum =
      ((removalPass ys c ρ).1.map (fun y => max (y-(removalPass ys c ρ).2) 0)).sum := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass]
    split_ifs with hy
    · have hm := threshold_mono ys (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))
      have hl : ρ ≤ ρ+(ρ-y)/((c-1:ℕ):ℝ) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy) (Nat.cast_nonneg _))
      have hz : max (y-(removalPass ys (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))).2) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr (hy.trans (hl.trans hm)))
      simpa only [List.map_cons,List.sum_cons,hz,zero_add] using ih (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))
    · simp only [List.map_cons,List.sum_cons]
      rw [ih]
lemma stable (ys : List ℝ) (c : ℕ) (ρ : ℝ)
    (he : (removalPass ys c ρ).1.length = ys.length) :
    removalPass ys c ρ = (ys,ρ) ∧ ∀ y ∈ ys, ρ < y := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass] at he ⊢
    split_ifs at he ⊢ with hy
    · have hlen := removalPass_length_le ys (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))
      simp only [List.length_cons] at he
      omega
    · simp only [List.length_cons,add_left_inj] at he
      have hh : (removalPass ys c ρ).1.length = ys.length := by omega
      obtain ⟨hr,hpos⟩ := ih c ρ hh
      rw [hr]
      exact ⟨rfl,by simpa using (show ρ<y ∧ ∀z∈ys,ρ<z from ⟨lt_of_not_ge hy,hpos⟩)⟩
lemma balance (a : ℝ) (ha : 0<a) (ys pre : List ℝ) (ρ : ℝ)
    (he : a = pre.sum+ys.sum-((pre.length+ys.length:ℕ):ℝ)*ρ) :
    a = pre.sum+(removalPass ys (pre.length+ys.length) ρ).1.sum-
      ((pre.length+(removalPass ys (pre.length+ys.length) ρ).1.length:ℕ):ℝ)*
        (removalPass ys (pre.length+ys.length) ρ).2 := by
  induction ys generalizing pre ρ with
  | nil => simpa [removalPass] using he
  | cons y ys ih =>
    have hc : pre.length+(y::ys).length = pre.length+ys.length+1 := by simp; omega
    rw [hc]
    simp only [removalPass]
    split_ifs with hy
    · have hn : 0 < pre.length+ys.length := by
        by_contra h
        have hp : pre=[] := List.length_eq_zero_iff.mp (by omega)
        have hs : ys=[] := List.length_eq_zero_iff.mp (by omega)
        subst pre; subst ys
        simp at he
        linarith
      have hn' : ((pre.length+ys.length:ℕ):ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      have hnEq : pre.length+ys.length+1-1 = pre.length+ys.length := by omega
      rw [hnEq]
      apply ih
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at he ⊢
      have hdiv : ((pre.length:ℝ)+(ys.length:ℝ))*((ρ-y)/((pre.length:ℝ)+(ys.length:ℝ))) = ρ-y := by
        apply mul_div_cancel₀
        simpa using hn'
      nlinarith
    · have hpre : (pre++[y]).length+ys.length = pre.length+ys.length+1 := by simp; omega
      have he' : a = (pre++[y]).sum+ys.sum-(((pre++[y]).length+ys.length:ℕ):ℝ)*ρ := by
        simpa [add_assoc,add_left_comm,add_comm] using he
      have h := ih (pre++[y]) ρ he'
      rw [hpre] at h
      simpa [add_assoc,add_left_comm,add_comm] using h
#print axioms balance
end CondatRemoval

open SimplexProj.Condat
namespace CondatRemoval
lemma hinge_sum_at (ys : List ℝ) (c : ℕ) (ρ τ : ℝ)
    (hτ : (removalPass ys c ρ).2 ≤ τ) :
    (ys.map (fun y => max (y-τ) 0)).sum =
      ((removalPass ys c ρ).1.map (fun y => max (y-τ) 0)).sum := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass] at hτ ⊢
    split_ifs at hτ ⊢ with hy
    · have hm := threshold_mono ys (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))
      have hl : ρ ≤ ρ+(ρ-y)/((c-1:ℕ):ℝ) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy) (Nat.cast_nonneg _))
      have hz : max (y-τ) 0 = 0 := max_eq_right (sub_nonpos.mpr (hy.trans (hl.trans (hm.trans hτ))))
      simpa only [List.map_cons,List.sum_cons,hz,zero_add] using ih (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ)) hτ
    · simp only [List.map_cons,List.sum_cons]
      rw [ih c ρ hτ]
lemma centered_sum (v : List ℝ) (ρ : ℝ) :
    (v.map (fun y => y-ρ)).sum = v.sum-(v.length:ℝ)*ρ := by
  induction v with
  | nil => simp
  | cons y v ih => simp [ih]; ring
lemma hinge_positive (v : List ℝ) (ρ : ℝ) (hp : ∀ y∈v,ρ<y) :
    (v.map (fun y => max (y-ρ) 0)).sum = v.sum-(v.length:ℝ)*ρ := by
  calc
    _ = (v.map (fun y => y-ρ)).sum := by
      congr 1
      apply List.map_congr_left
      intro y hy
      exact max_eq_left (sub_nonneg.mpr (hp y hy).le)
    _ = _ := centered_sum v ρ

theorem loop_spec (a : ℝ) (ha : 0<a) (v : List ℝ) (ρ : ℝ)
    (he : a = v.sum-(v.length:ℝ)*ρ) :
    ρ ≤ (removalLoop v ρ).2 ∧
    (removalLoop v ρ).1.Sublist v ∧
    a = (removalLoop v ρ).1.sum-((removalLoop v ρ).1.length:ℝ)*(removalLoop v ρ).2 ∧
    (∀ y∈(removalLoop v ρ).1,(removalLoop v ρ).2<y) ∧
    (v.map (fun y => max (y-(removalLoop v ρ).2) 0)).sum = a := by
  let r := removalPass v v.length ρ
  have hr : a = r.1.sum-(r.1.length:ℝ)*r.2 := by
    simpa [r] using balance a ha v [] ρ (by simpa using he)
  have hmono : ρ≤r.2 := threshold_mono v v.length ρ
  have hsub : r.1.Sublist v := sublist v v.length ρ
  have hlen : r.1.length≤v.length := removalPass_length_le v v.length ρ
  have hdef : removalLoop v ρ = if r.1.length=v.length then r else removalLoop r.1 r.2 := by
    rw [removalLoop]
  rw [hdef]
  split_ifs with hs
  · obtain ⟨hsame,hpos⟩ := stable v v.length ρ hs
    change r=(v,ρ) at hsame
    rw [hsame]
    exact ⟨le_rfl,List.Sublist.refl _,he,hpos,(hinge_positive v ρ hpos).trans he.symm⟩
  · have hlt : r.1.length<v.length := lt_of_le_of_ne hlen hs
    have ih := loop_spec a ha r.1 r.2 hr
    refine ⟨hmono.trans ih.1,ih.2.1.trans hsub,ih.2.2.1,ih.2.2.2.1,?_⟩
    exact (hinge_sum_at v v.length ρ (removalLoop r.1 r.2).2 ih.1).trans ih.2.2.2.2
termination_by v.length
#print axioms loop_spec
end CondatRemoval

open SimplexProj.Condat
open scoped BigOperators
namespace CondatRemoval
lemma threshold_projection {N : ℕ} (a τ : ℝ) (y : Fin N → ℝ)
    (hs : ∑ i, max (y i-τ) 0 = a) :
    IsSimplexProjection a y (fun i => max (y i-τ) 0) := by
  refine ⟨⟨hs,fun i => le_max_right _ _⟩,?_⟩
  intro z hz
  have hp (i : Fin N) : (max (y i-τ) 0-y i)^2 ≤
      (z i-y i)^2 + 2*τ*(z i-max (y i-τ) 0) := by
    by_cases h : 0 ≤ y i-τ
    · rw [max_eq_left h]
      nlinarith [sq_nonneg (z i-(y i-τ))]
    · rw [max_eq_right (le_of_not_ge h)]
      have hprod := mul_nonneg (hz.2 i) (show 0≤τ-y i by linarith)
      nlinarith [sq_nonneg (z i)]
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hp i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,hs,hz.1,sub_self,mul_zero,add_zero] at ht
  exact ht
lemma filter_pass (ys : List ℝ) (c : ℕ) (ρ τ : ℝ)
    (hτ : (removalPass ys c ρ).2 ≤ τ) :
    ys.filter (fun y => decide (τ<y)) = (removalPass ys c ρ).1.filter (fun y => decide (τ<y)) := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    simp only [removalPass] at hτ ⊢
    split_ifs at hτ ⊢ with hy
    · have hm := threshold_mono ys (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ))
      have hl : ρ ≤ ρ+(ρ-y)/((c-1:ℕ):ℝ) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy) (Nat.cast_nonneg _))
      have hz : ¬τ<y := not_lt.mpr (hy.trans (hl.trans (hm.trans hτ)))
      simpa [List.filter_cons,hz] using ih (c-1) (ρ+(ρ-y)/((c-1:ℕ):ℝ)) hτ
    · simp only [List.filter_cons]
      rw [ih c ρ hτ]
theorem loop_filter (a : ℝ) (ha : 0<a) (v : List ℝ) (ρ : ℝ)
    (he : a=v.sum-(v.length:ℝ)*ρ) :
    v.filter (fun y => decide ((removalLoop v ρ).2<y)) = (removalLoop v ρ).1 := by
  let r := removalPass v v.length ρ
  have hr : a = r.1.sum-(r.1.length:ℝ)*r.2 := by
    simpa [r] using balance a ha v [] ρ (by simpa using he)
  have hdef : removalLoop v ρ = if r.1.length=v.length then r else removalLoop r.1 r.2 := by
    rw [removalLoop]
  rw [hdef]
  split_ifs with hs
  · obtain ⟨hsame,hpos⟩ := stable v v.length ρ hs
    change r=(v,ρ) at hsame
    rw [hsame]
    apply List.filter_eq_self.mpr
    intro y hy
    simpa using hpos y hy
  · have hlt : r.1.length<v.length := lt_of_le_of_ne (removalPass_length_le _ _ _) hs
    have hm := (loop_spec a ha r.1 r.2 hr).1
    exact (filter_pass v v.length ρ (removalLoop r.1 r.2).2 hm).trans (loop_filter a ha r.1 r.2 hr)
termination_by v.length
#print axioms loop_filter
end CondatRemoval

open SimplexProj.Condat
open scoped BigOperators
namespace CondatRemoval
lemma filter_length_sum (ys : List ℝ) (p : ℝ → Bool) :
    (ys.filter p).length = (ys.map (fun y => if p y then (1:ℕ) else 0)).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.filter_cons,List.map_cons,List.sum_cons]
    split_ifs <;> simp_all <;> omega
lemma count_ofFn {N : ℕ} (y : Fin N → ℝ) (τ : ℝ) :
    ((List.ofFn y).filter (fun z => decide (τ<z))).length =
      (Finset.univ.filter (fun i => τ<y i)).card := by
  classical
  rw [filter_length_sum]
  rw [List.map_ofFn,List.sum_ofFn,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp
theorem finite_certificate (N : ℕ) (a : ℝ) (ha : 0<a) (y : Fin N → ℝ) (ρ : ℝ)
    (he : a = (∑ i,y i)-(N:ℝ)*ρ) :
    let r := removalLoop (List.ofFn y) ρ
    IsSimplexProjection a y (fun i => max (y i-r.2) 0) ∧
      r.1.length = (Finset.univ.filter (fun i => max (y i-r.2) 0 ≠ 0)).card := by
  classical
  let v := List.ofFn y
  have hb : a=v.sum-(v.length:ℝ)*ρ := by simpa [v,List.sum_ofFn] using he
  have h := loop_spec a ha v ρ hb
  constructor
  · apply threshold_projection
    simpa [v,List.map_ofFn,List.sum_ofFn] using h.2.2.2.2
  · have hc := congrArg List.length (loop_filter a ha v ρ hb)
    rw [show v=List.ofFn y from rfl,count_ofFn] at hc
    rw [← hc]
    congr 1
    ext i
    simp [max_eq_right_iff,sub_nonpos,not_le]
#print axioms finite_certificate
end CondatRemoval

open SimplexProj.Condat
namespace CondatScan
lemma append_balance (a ρ y : ℝ) (v : List ℝ)
    (hb : a=v.sum-(v.length:ℝ)*ρ) :
    a=(v++[y]).sum-((v++[y]).length:ℝ)*(ρ+(y-ρ)/((v.length:ℝ)+1)) := by
  have hn : (v.length:ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  simp only [List.sum_append,List.sum_singleton,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
  rw [mul_add, mul_div_cancel₀ _ hn]
  linarith
lemma first_step (a y : ℝ) (s : List ℝ × List ℝ × ℝ)
    (hb : a=s.2.1.sum-(s.2.1.length:ℝ)*s.2.2) :
    let r := firstPassStep a s y
    s.2.2 ≤ r.2.2 ∧ a=r.2.1.sum-(r.2.1.length:ℝ)*r.2.2 ∧
    ∀ τ, r.2.2 ≤ τ →
      ((s.1++s.2.1)++[y]).filter (fun z => decide (τ<z)) =
        (r.1++r.2.1).filter (fun z => decide (τ<z)) := by
  rcases s with ⟨vt,v,ρ⟩
  dsimp only at hb ⊢
  unfold firstPassStep
  dsimp only
  split_ifs with hy hnew
  · have hm : ρ ≤ ρ+(y-ρ)/((v.length:ℝ)+1) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy.le) (by positivity))
    refine ⟨hm,append_balance a ρ y v hb,?_⟩
    intro τ hτ
    simp only [List.append_assoc]
  · have hm : ρ ≤ ρ+(y-ρ)/((v.length:ℝ)+1) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy.le) (by positivity))
    refine ⟨hm.trans (le_of_not_gt hnew),?_,?_⟩
    · simp
    · intro τ hτ; rfl
  · refine ⟨le_rfl,hb,?_⟩
    intro τ hτ
    have hz : ¬τ<y := not_lt.mpr ((le_of_not_gt hy).trans hτ)
    simp [List.filter_append,hz]
theorem first_fold (a : ℝ) (ys : List ℝ) (s : List ℝ × List ℝ × ℝ)
    (hb : a=s.2.1.sum-(s.2.1.length:ℝ)*s.2.2) :
    let r := ys.foldl (firstPassStep a) s
    s.2.2 ≤ r.2.2 ∧ a=r.2.1.sum-(r.2.1.length:ℝ)*r.2.2 ∧
    ∀ τ, r.2.2 ≤ τ →
      ((s.1++s.2.1)++ys).filter (fun z => decide (τ<z)) =
        (r.1++r.2.1).filter (fun z => decide (τ<z)) := by
  induction ys generalizing s with
  | nil =>
    simp only [List.foldl_nil,List.append_nil]
    exact ⟨le_rfl,hb,fun _ _ => True.intro⟩
  | cons y ys ih =>
    dsimp only [List.foldl_cons]
    have hs := first_step a y s hb
    have hi := ih (firstPassStep a s y) hs.2.1
    refine ⟨hs.1.trans hi.1,hi.2.1,?_⟩
    intro τ hτ
    have hh := hs.2.2 τ (hi.1.trans hτ)
    calc
      _ = (((s.1++s.2.1)++[y])++ys).filter (fun z => decide (τ<z)) := by simp only [List.append_assoc,List.singleton_append]
      _ = (((firstPassStep a s y).1++(firstPassStep a s y).2.1)++ys).filter (fun z => decide (τ<z)) := by simpa only [List.filter_append] using congrArg (fun l : List ℝ => l ++ ys.filter (fun z => decide (τ<z))) hh
      _ = _ := hi.2.2 τ hτ
#print axioms first_fold
end CondatScan

open SimplexProj.Condat
namespace CondatScan
lemma cleanup_step (a y : ℝ) (s : List ℝ × ℝ)
    (hb : a=s.1.sum-(s.1.length:ℝ)*s.2) :
    let r := cleanupStep s y
    s.2 ≤ r.2 ∧ a=r.1.sum-(r.1.length:ℝ)*r.2 ∧
    ∀ τ, r.2 ≤ τ →
      (s.1++[y]).filter (fun z => decide (τ<z)) =
        r.1.filter (fun z => decide (τ<z)) := by
  rcases s with ⟨v,ρ⟩
  dsimp only at hb ⊢
  unfold cleanupStep
  dsimp only
  split_ifs with hy
  · simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    refine ⟨le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hy.le) (by positivity)),by simpa only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one] using append_balance a ρ y v hb,?_⟩
    intro τ hτ; trivial
  · refine ⟨le_rfl,hb,?_⟩
    intro τ hτ
    have hz : ¬τ<y := not_lt.mpr ((le_of_not_gt hy).trans hτ)
    simp [List.filter_append,hz]
theorem cleanup_fold (a : ℝ) (ys : List ℝ) (s : List ℝ × ℝ)
    (hb : a=s.1.sum-(s.1.length:ℝ)*s.2) :
    let r := ys.foldl cleanupStep s
    s.2 ≤ r.2 ∧ a=r.1.sum-(r.1.length:ℝ)*r.2 ∧
    ∀ τ, r.2 ≤ τ →
      (s.1++ys).filter (fun z => decide (τ<z)) =
        r.1.filter (fun z => decide (τ<z)) := by
  induction ys generalizing s with
  | nil =>
    simp only [List.foldl_nil,List.append_nil]
    exact ⟨le_rfl,hb,fun _ _ => True.intro⟩
  | cons y ys ih =>
    dsimp only [List.foldl_cons]
    have hs := cleanup_step a y s hb
    have hi := ih (cleanupStep s y) hs.2.1
    refine ⟨hs.1.trans hi.1,hi.2.1,?_⟩
    intro τ hτ
    calc
      _ = ((s.1++[y])++ys).filter (fun z => decide (τ<z)) := by simp only [List.append_assoc,List.singleton_append]
      _ = ((cleanupStep s y).1++ys).filter (fun z => decide (τ<z)) := by simpa only [List.filter_append] using congrArg (fun l : List ℝ => l ++ ys.filter (fun z => decide (τ<z))) (hs.2.2 τ (hi.1.trans hτ))
      _ = _ := hi.2.2 τ hτ
#print axioms cleanup_fold
end CondatScan

open SimplexProj.Condat
open scoped BigOperators
namespace CondatScan
lemma hinge_filter (v : List ℝ) (τ : ℝ) :
    (v.map (fun z => max (z-τ) 0)).sum =
      ((v.filter (fun z => decide (τ<z))).map (fun z => max (z-τ) 0)).sum := by
  induction v with
  | nil => simp
  | cons y ys ih =>
    by_cases h : τ<y
    · simp [h,ih]
    · have hz : max (y-τ) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
      simp [h,hz,ih]
theorem passes_spec (a : ℝ) (ha : 0<a) (y : ℝ) (ys : List ℝ) :
    let s2 := ys.foldl (firstPassStep a) ([],[y],y-a)
    let s3 := s2.1.foldl cleanupStep (s2.2.1,s2.2.2)
    let s4 := removalLoop s3.1 s3.2
    (y::ys).filter (fun z => decide (s4.2<z)) |>.Perm s4.1 := by
  dsimp only
  let s2 := ys.foldl (firstPassStep a) ([],[y],y-a)
  let s3 := s2.1.foldl cleanupStep (s2.2.1,s2.2.2)
  let s4 := removalLoop s3.1 s3.2
  have h2 := first_fold a ys ([],[y],y-a) (by simp)
  change y-a ≤ s2.2.2 ∧ a=s2.2.1.sum-(s2.2.1.length:ℝ)*s2.2.2 ∧ _ at h2
  have h3 := cleanup_fold a s2.1 (s2.2.1,s2.2.2) h2.2.1
  have h4 := CondatRemoval.loop_spec a ha s3.1 s3.2 h3.2.1
  have hf4 := CondatRemoval.loop_filter a ha s3.1 s3.2 h3.2.1
  change s3.1.filter (fun z => decide (s4.2<z)) = s4.1 at hf4
  have hf2 := h2.2.2 s4.2 (h3.1.trans h4.1)
  have hf3 := h3.2.2 s4.2 h4.1
  change ((y::ys).filter (fun z => decide (s4.2<z))).Perm s4.1
  simp only [List.nil_append,List.singleton_append] at hf2
  rw [hf2,List.filter_append]
  have hp : ((s2.1.filter (fun z => decide (s4.2<z))) ++ (s2.2.1.filter (fun z => decide (s4.2<z)))).Perm
      ((s2.2.1++s2.1).filter (fun z => decide (s4.2<z))) := by
    rw [List.filter_append]
    exact List.perm_append_comm
  exact hp.trans (List.Perm.of_eq (hf3.trans hf4))
theorem algorithm_list (a : ℝ) (ha : 0<a) (y : ℝ) (ys : List ℝ) :
    let r := condatAlgorithm a (y::ys)
    ((y::ys).map (fun z => max (z-r.1) 0)).sum = a ∧
    r.2 = ((y::ys).filter (fun z => decide (r.1<z))).length := by
  let s2 := ys.foldl (firstPassStep a) ([],[y],y-a)
  let s3 := s2.1.foldl cleanupStep (s2.2.1,s2.2.2)
  let s4 := removalLoop s3.1 s3.2
  have h2 := first_fold a ys ([],[y],y-a) (by simp)
  have h3 := cleanup_fold a s2.1 (s2.2.1,s2.2.2) h2.2.1
  have h4 := CondatRemoval.loop_spec a ha s3.1 s3.2 h3.2.1
  have hp := passes_spec a ha y ys
  change ((y::ys).filter (fun z => decide (s4.2<z))).Perm s4.1 at hp
  change ((y::ys).map (fun z => max (z-s4.2) 0)).sum = a ∧
    s4.1.length = ((y::ys).filter (fun z => decide (s4.2<z))).length
  constructor
  · rw [hinge_filter]
    calc
      _ = (s4.1.map (fun z => max (z-s4.2) 0)).sum := (hp.map _).sum_eq
      _ = s4.1.sum-(s4.1.length:ℝ)*s4.2 := CondatRemoval.hinge_positive _ _ h4.2.2.2.1
      _ = a := h4.2.2.1.symm
  · exact hp.length_eq.symm
#print axioms algorithm_list
end CondatScan

open SimplexProj.Condat
open scoped BigOperators
set_option maxHeartbeats 800000

theorem solution (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a) (y : Fin N → ℝ)
    (τ : ℝ) (K : ℕ) (hout : condatAlgorithm a (List.ofFn y) = (τ, K)) :
    IsSimplexProjection a y (fun n => max (y n - τ) 0) ∧
      K = (Finset.univ.filter (fun n => max (y n - τ) 0 ≠ 0)).card := by
  classical
  have hn : List.ofFn y ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn,List.length_nil] at hlen
    omega
  obtain ⟨v,vs,hvs⟩ := List.exists_cons_of_ne_nil hn
  have hp := CondatScan.algorithm_list a ha v vs
  rw [← hvs,hout] at hp
  dsimp only at hp
  constructor
  · apply CondatRemoval.threshold_projection
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using hp.1
  · rw [hp.2,CondatRemoval.count_ofFn]
    congr 1
    ext i
    simp [max_eq_right_iff,sub_nonpos,not_le]
#print axioms solution
