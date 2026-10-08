-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:35:46.116432+00:00
-- url     : https://prove2.me/submissions/92fd93d7-aca8-432b-8f3b-28698ef3078e

import Definitions.Def_WorstCaseCVaR_Mixture_Setting
import Mathlib

section
set_option autoImplicit false
namespace MixtureCodex

lemma convex_strict_combo (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (t z r u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v) (hs : u+v=1)
    (hr : u*t+v*z=r) (hz : g z < g t) : g r < g t := by
  have hc := hg.2 (Set.mem_univ t) (Set.mem_univ z) hu hv.le hs
  simp only [smul_eq_mul] at hc
  rw [hr] at hc
  have he : u*g t+v*g t = g t := by
    calc
      _ = (u+v)*g t := by ring
      _ = _ := by rw [hs,one_mul]
  have hl : u*g t+v*g z < u*g t+v*g t := by
    nlinarith [mul_pos hv (sub_pos.mpr hz)]
  rw [he] at hl
  exact hc.trans_lt hl

lemma convex_left_decrease (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a b : ℝ) (hab : a ≤ b)
    (hm : {q : ℝ | IsMinOn g Set.univ q} = Set.Icc a b)
    (t r : ℝ) (htr : t < r) (hra : r ≤ a) : g r < g t := by
  have hmin : IsMinOn g Set.univ a := by
    change a ∈ {q : ℝ | IsMinOn g Set.univ q}
    rw [hm]
    exact ⟨le_rfl,hab⟩
  have hn : ¬ IsMinOn g Set.univ t := by
    intro ht
    have hh : t ∈ Set.Icc a b := by rw [← hm]; exact ht
    linarith [hh.1]
  have hval : g a < g t := by
    have hle := isMinOn_iff.mp hmin t (Set.mem_univ t)
    by_contra hlt
    have he := le_antisymm hle (le_of_not_gt hlt)
    apply hn
    apply isMinOn_iff.mpr
    intro q hq
    rw [← he]
    exact isMinOn_iff.mp hmin q hq
  have hd : 0 < a-t := by linarith
  let u := (a-r)/(a-t)
  let v := (r-t)/(a-t)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hra) hd.le
  have hv : 0 < v := div_pos (sub_pos.mpr htr) hd
  have hs : u+v=1 := by dsimp [u,v]; field_simp; ring
  have hp : u*t+v*a=r := by dsimp [u,v]; field_simp; ring
  exact convex_strict_combo g hg t a r u v hu hv hs hp hval

lemma convex_right_increase (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a b : ℝ) (hab : a ≤ b)
    (hm : {q : ℝ | IsMinOn g Set.univ q} = Set.Icc a b)
    (r t : ℝ) (hbr : b ≤ r) (hrt : r < t) : g r < g t := by
  have hmin : IsMinOn g Set.univ b := by
    change b ∈ {q : ℝ | IsMinOn g Set.univ q}
    rw [hm]
    exact ⟨hab,le_rfl⟩
  have hn : ¬ IsMinOn g Set.univ t := by
    intro ht
    have hh : t ∈ Set.Icc a b := by rw [← hm]; exact ht
    linarith [hh.2]
  have hval : g b < g t := by
    have hle := isMinOn_iff.mp hmin t (Set.mem_univ t)
    by_contra hlt
    have he := le_antisymm hle (le_of_not_gt hlt)
    apply hn
    apply isMinOn_iff.mpr
    intro q hq
    rw [← he]
    exact isMinOn_iff.mp hmin q hq
  have hd : 0 < t-b := by linarith
  let u := (r-b)/(t-b)
  let v := (t-r)/(t-b)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbr) hd.le
  have hv : 0 < v := div_pos (sub_pos.mpr hrt) hd
  have hs : u+v=1 := by dsimp [u,v]; field_simp; ring
  have hp : u*t+v*b=r := by dsimp [u,v]; field_simp; ring
  exact convex_strict_combo g hg t b r u v hu hv hs hp hval

end MixtureCodex

end


section
set_option autoImplicit false
namespace MixtureCodex
lemma weighted_convex {l : ℕ} (g : Fin l → ℝ → ℝ)
    (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) (c : Fin l → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ConvexOn ℝ Set.univ (fun t => ∑ i, c i * g i t) := by
  refine ⟨convex_univ, ?_⟩
  intro t ht r hr u v hu hv huv
  simp only [smul_eq_mul]
  calc
    _ ≤ ∑ i, c i * (u * g i t + v * g i r) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hc i)
      simpa only [smul_eq_mul] using (hg i).2 ht hr hu hv huv
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma weighted_argmin_bounds {l : ℕ} [NeZero l] (g : Fin l → ℝ → ℝ)
    (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) (a b : Fin l → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hm : ∀ i, {q : ℝ | IsMinOn (g i) Set.univ q} = Set.Icc (a i) (b i))
    (c : Fin l → ℝ) (hc : ∀ i, 0 ≤ c i) (hp : ∃ i, 0 < c i) :
    {q : ℝ | IsMinOn (fun t => ∑ i, c i * g i t) Set.univ q} ⊆
      Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
        (Finset.univ.sup' Finset.univ_nonempty b) := by
  classical
  let A := Finset.univ.inf' Finset.univ_nonempty a
  let B := Finset.univ.sup' Finset.univ_nonempty b
  have ha (i : Fin l) : A ≤ a i := Finset.inf'_le a (Finset.mem_univ i)
  have hb (i : Fin l) : b i ≤ B := Finset.le_sup' b (Finset.mem_univ i)
  intro t ht
  change IsMinOn (fun t => ∑ i, c i * g i t) Set.univ t at ht
  rcases hp with ⟨j,hj⟩
  constructor
  · by_contra hn
    have hlt : t < A := lt_of_not_ge hn
    have hgi (i : Fin l) : g i A < g i t :=
      convex_left_decrease (g i) (hg i) (a i) (b i) (hab i) (hm i) t A hlt (ha i)
    have hs : (∑ i, c i * g i A) < ∑ i, c i * g i t := by
      apply Finset.sum_lt_sum
      · intro i hi; exact mul_le_mul_of_nonneg_left (hgi i).le (hc i)
      · exact ⟨j,Finset.mem_univ j,mul_lt_mul_of_pos_left (hgi j) hj⟩
    exact (not_lt_of_ge (isMinOn_iff.mp ht A (Set.mem_univ A))) hs
  · by_contra hn
    have hlt : B < t := lt_of_not_ge hn
    have hgi (i : Fin l) : g i B < g i t :=
      convex_right_increase (g i) (hg i) (a i) (b i) (hab i) (hm i) B t (hb i) hlt
    have hs : (∑ i, c i * g i B) < ∑ i, c i * g i t := by
      apply Finset.sum_lt_sum
      · intro i hi; exact mul_le_mul_of_nonneg_left (hgi i).le (hc i)
      · exact ⟨j,Finset.mem_univ j,mul_lt_mul_of_pos_left (hgi j) hj⟩
    exact (not_lt_of_ge (isMinOn_iff.mp ht B (Set.mem_univ B))) hs
end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma hinge_integrable {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : Integrable (f x) P) (α : ℝ) : Integrable (fun y ↦ max (f x y-α) 0) P :=
  (hf.sub (integrable_const α)).pos_part

lemma mixture_integrable {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (g : (Fin m → ℝ) → ℝ) (hg : ∀ i, Integrable g (P i)) (lam : Fin l → ℝ) :
    Integrable g (mixture P lam) := by
  unfold mixture
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (hg i).smul_measure ENNReal.ofReal_ne_top

lemma mixture_isProbability {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) : IsProbabilityMeasure (mixture P lam) := by
  constructor
  unfold mixture
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ h.1 i),h.2]
  simp

lemma mixture_hinge_integral {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) (α : ℝ) :
    (∫ y, max (f x y-α) 0 ∂(mixture P lam)) =
      ∑ i, lam i * ∫ y, max (f x y-α) 0 ∂P i := by
  unfold mixture
  rw [integral_finsetSum_measure (fun i hi ↦
    (hinge_integrable (P i) f x (hf i) α).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure,ENNReal.toReal_ofReal (h.1 i),smul_eq_mul]

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex

theorem eq_53 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l), ∀ α : ℝ,
      Hfun P f β x α lam = ∑ i, lam i * Fi P f β x i α := by
  intro lam hlam α
  simp only [Hfun,Fi,ruFun]
  rw [mixture_hinge_integral P f x hf lam hlam α]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hlam.2,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring


end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma ru_convex {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) : ConvexOn ℝ Set.univ (ruFun P f β x) := by
  refine ⟨convex_univ,?_⟩
  intro a ha b hb u v hu hv huv
  simp only [smul_eq_mul]
  have hh : (fun y ↦ max (f x y-(u*a+v*b)) 0) ≤ᵐ[P]
      (fun y ↦ u*max (f x y-a) 0 + v*max (f x y-b) 0) := by
    apply Filter.Eventually.of_forall
    intro y
    apply max_le
    · calc
        _ = u*(f x y-a)+v*(f x y-b) := by linear_combination -(f x y)*huv
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
    · exact add_nonneg (mul_nonneg hu (le_max_right _ _)) (mul_nonneg hv (le_max_right _ _))
  have hi := integral_mono_ae (hinge_integrable P f x hf (u*a+v*b))
    (((hinge_integrable P f x hf a).const_mul u).add ((hinge_integrable P f x hf b).const_mul v)) hh
  change (∫ y, max (f x y-(u*a+v*b)) 0 ∂P) ≤
    (∫ y, u*max (f x y-a) 0 + v*max (f x y-b) 0 ∂P) at hi
  rw [integral_add ((hinge_integrable P f x hf a).const_mul u)
    ((hinge_integrable P f x hf b).const_mul v),integral_const_mul,integral_const_mul] at hi
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have he := mul_le_mul_of_nonneg_left hi hc
  dsimp [ruFun]
  nlinarith [he]

lemma hinge_integral_difference {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : Integrable (f x) P) (a b : ℝ) :
    |(∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)| ≤ |a-b| := by
  rw [← integral_sub (hinge_integrable P f x hf a) (hinge_integrable P f x hf b)]
  have hh : ∀ᵐ y ∂P, ‖max (f x y-a) 0-max (f x y-b) 0‖ ≤ |a-b| := by
    apply Filter.Eventually.of_forall
    intro y
    have he : (f x y-a)-(f x y-b) = b-a := by ring
    simpa only [Real.norm_eq_abs,he,abs_sub_comm] using
      abs_max_sub_max_le_abs (f x y-a) (f x y-b) 0
  simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const hh

lemma ru_continuous {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) : Continuous (ruFun P f β x) := by
  let c := (1-β)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (by linarith)
  let K : NNReal := ⟨1+c,by linarith⟩
  have hL : LipschitzWith K (ruFun P f β x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq,Real.dist_eq]
    change |ruFun P f β x a-ruFun P f β x b| ≤ (1+c)*|a-b|
    have he : ruFun P f β x a-ruFun P f β x b =
        (a-b)+c*((∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)) := by
      dsimp [ruFun,c]
      ring
    rw [he]
    calc
      _ ≤ |a-b|+|c*((∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P))| := abs_add_le _ _
      _ = |a-b|+c*|(∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)| := by
        rw [abs_mul,abs_of_nonneg hc]
      _ ≤ (1+c)*|a-b| := by
        have hh := mul_le_mul_of_nonneg_left (hinge_integral_difference P f x hf a b) hc
        nlinarith [hh]
  exact hL.continuous

lemma ru_lower_bounds {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) (a : ℝ) :
    a ≤ ruFun P f β x a ∧
    (1-β)⁻¹*(∫ y, f x y ∂P)+(1-(1-β)⁻¹)*a ≤ ruFun P f β x a := by
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp : 0 ≤ ∫ y, max (f x y-a) 0 ∂P := integral_nonneg (fun y ↦ le_max_right _ _)
  have hle := integral_mono_ae (hf.sub (integrable_const a)) (hinge_integrable P f x hf a)
    (Filter.Eventually.of_forall (fun y ↦ le_max_left (f x y-a) 0))
  change (∫ y, f x y-a ∂P) ≤ (∫ y, max (f x y-a) 0 ∂P) at hle
  rw [integral_sub hf (integrable_const a)] at hle
  simp only [integral_const,probReal_univ,one_smul] at hle
  have hh := mul_le_mul_of_nonneg_left hle hc
  constructor <;> dsimp [ruFun] <;> nlinarith [mul_nonneg hc hp,hh]

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory Set
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma ru_sublevel_compact {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) (t : ℝ) :
    IsCompact {a : ℝ | ruFun P f β x a ≤ t} := by
  let c := (1-β)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  have he : c*(1-β) = 1 := inv_mul_cancel₀ (by linarith)
  have hcone : 1 < c := by nlinarith [mul_pos hc hβ0]
  let L := (c*(∫ y, f x y ∂P)-t)/(c-1)
  have hs : {a : ℝ | ruFun P f β x a ≤ t} ⊆ Icc L t := by
    intro a ha
    have hb := ru_lower_bounds P f β hβ1 x hf a
    refine ⟨?_,hb.1.trans ha⟩
    change (c*(∫ y, f x y ∂P)-t)/(c-1) ≤ a
    apply (div_le_iff₀ (by linarith)).mpr
    have hh : c*(∫ y, f x y ∂P)+(1-c)*a ≤ t := hb.2.trans ha
    nlinarith [hh]
  have hclosed : IsClosed {a : ℝ | ruFun P f β x a ≤ t} :=
    isClosed_Iic.preimage (ru_continuous P f β hβ1 x hf)
  exact isCompact_Icc.of_isClosed_subset hclosed hs

lemma ru_min_exists {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a : ℝ, IsMinOn (ruFun P f β x) univ a := by
  let A := {a : ℝ | ruFun P f β x a ≤ ruFun P f β x 0}
  have h0 : (0 : ℝ) ∈ A := by
    change ruFun P f β x 0 ≤ ruFun P f β x 0
    exact le_rfl
  have hc : IsCompact A := ru_sublevel_compact P f β hβ0 hβ1 x hf _
  obtain ⟨a,ha,hm⟩ := hc.exists_isMinOn ⟨0,h0⟩ (ru_continuous P f β hβ1 x hf).continuousOn
  refine ⟨a,isMinOn_iff.mpr ?_⟩
  intro b hb
  by_cases hba : b ∈ A
  · exact isMinOn_iff.mp hm b hba
  · exact (isMinOn_iff.mp hm 0 h0).trans (le_of_lt (lt_of_not_ge hba))

lemma argmin_interval_complete {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a b : ℝ, a ≤ b ∧ {α : ℝ | IsMinOn (ruFun P f β x) Set.univ α} = Set.Icc a b := by
  obtain ⟨q,hq⟩ := ru_min_exists P f β hβ0 hβ1 x hf
  let A := {a : ℝ | IsMinOn (ruFun P f β x) univ a}
  have he : A = {a : ℝ | ruFun P f β x a ≤ ruFun P f β x q} := by
    ext a
    constructor
    · intro ha
      exact isMinOn_iff.mp ha q (mem_univ q)
    · intro ha
      apply isMinOn_iff.mpr
      intro b hb
      exact ha.trans (isMinOn_iff.mp hq b hb)
  have hc : IsCompact A := by rw [he]; exact ru_sublevel_compact P f β hβ0 hβ1 x hf _
  have hne : A.Nonempty := ⟨q,hq⟩
  have hcv : Convex ℝ A := by
    rw [he]
    simpa only [mem_univ,true_and] using (ru_convex P f β hβ1 x hf).convex_le (ruFun P f β x q)
  have hi : A = Icc (sInf A) (sSup A) := eq_Icc_of_connected_compact (hcv.isConnected hne) hc
  have hab : sInf A ≤ sSup A := (csInf_le hc.bddBelow (hne.choose_spec)).trans
    (le_csSup hc.bddAbove hne.choose_spec)
  exact ⟨sInf A,sSup A,hab,hi⟩

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex

theorem argmin_H_subset {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i))
    (a b : Fin l → ℝ)
    (hab : ∀ i, {α : ℝ | IsMinOn (Fi P f β x i) Set.univ α} = Set.Icc (a i) (b i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l),
      {α : ℝ | IsMinOn (fun α => Hfun P f β x α lam) Set.univ α} ⊆
          Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
            (Finset.univ.sup' Finset.univ_nonempty b) ∧
        ∃ α₀ ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
            (Finset.univ.sup' Finset.univ_nonempty b),
          IsMinOn (fun α => Hfun P f β x α lam) Set.univ α₀ := by
  classical
  have hle (i : Fin l) : a i ≤ b i := by
    obtain ⟨q,hq⟩ := ru_min_exists (P i) f β hβ0 hβ1 x (hf i)
    have hmem : q ∈ Set.Icc (a i) (b i) := by rw [← hab i]; exact hq
    exact hmem.1.trans hmem.2
  intro lam hlam
  have hpos : ∃ i, 0 < lam i := by
    by_contra hn
    push Not at hn
    have hz (i : Fin l) : lam i = 0 := le_antisymm (hn i) (hlam.1 i)
    have hs := hlam.2
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  have he : (fun α => Hfun P f β x α lam) = (fun α => ∑ i, lam i * Fi P f β x i α) :=
    funext (eq_53 P f β hβ0 hβ1 x hf lam hlam)
  have hs : {α : ℝ | IsMinOn (fun α => Hfun P f β x α lam) Set.univ α} ⊆
      Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
        (Finset.univ.sup' Finset.univ_nonempty b) := by
    rw [he]
    exact weighted_argmin_bounds (Fi P f β x) (fun i => ru_convex (P i) f β hβ1 x (hf i))
      a b hle hab lam hlam.1 hpos
  let := mixture_isProbability P lam hlam
  obtain ⟨q,hq⟩ := ru_min_exists (mixture P lam) f β hβ0 hβ1 x (mixture_integrable P (f x) hf lam)
  exact ⟨hs,q,hs hq,hq⟩

end MixtureCodex


end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex
lemma H_continuous_lam {l m n : ℕ} [NeZero l]
    (P : Fin l → Measure (Fin m → ℝ)) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (α : ℝ) :
    ContinuousOn (Hfun P f β x α) (stdSimplex ℝ (Fin l)) := by
  have hc : Continuous (fun lam : Fin l → ℝ => ∑ i, lam i * Fi P f β x i α) := by
    fun_prop
  apply hc.continuousOn.congr
  intro lam hlam
  exact eq_53 P f β hβ0 hβ1 x hf lam hlam α

lemma H_concave_lam {l m n : ℕ} [NeZero l]
    (P : Fin l → Measure (Fin m → ℝ)) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (α : ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin l)) (Hfun P f β x α) := by
  refine ⟨convex_stdSimplex ℝ (Fin l),?_⟩
  intro lam hl mu hm u v hu hv huv
  have hmix := (convex_stdSimplex ℝ (Fin l)) hl hm hu hv huv
  rw [eq_53 P f β hβ0 hβ1 x hf lam hl α,
    eq_53 P f β hβ0 hβ1 x hf mu hm α,
    eq_53 P f β hβ0 hβ1 x hf _ hmix α]
  simp only [smul_eq_mul,Pi.add_apply,Pi.smul_apply]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  ring
end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex
lemma common_saddle {l m n : ℕ} [NeZero l]
    (P : Fin l → Measure (Fin m → ℝ)) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (a b : Fin l → ℝ)
    (hab : ∀ i, {α : ℝ | IsMinOn (Fi P f β x i) Set.univ α} = Set.Icc (a i) (b i)) :
    ∃ α₀ ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
        (Finset.univ.sup' Finset.univ_nonempty b),
      ∃ lam₀ ∈ stdSimplex ℝ (Fin l),
        IsMinOn (fun α => Hfun P f β x α lam₀) Set.univ α₀ ∧
        (∀ lam ∈ stdSimplex ℝ (Fin l), Hfun P f β x α₀ lam ≤ Hfun P f β x α₀ lam₀) := by
  classical
  let A := Finset.univ.inf' Finset.univ_nonempty a
  let B := Finset.univ.sup' Finset.univ_nonempty b
  let I := Set.Icc A B
  let S := stdSimplex ℝ (Fin l)
  have hSne : S.Nonempty := ⟨Pi.single (0 : Fin l) 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨q,hq,hmin⟩ := (argmin_H_subset P f β hβ0 hβ1 x hf a b hab hSne.choose hSne.choose_spec).2
  have hIne : I.Nonempty := ⟨q,hq⟩
  have hlsc (lam) (hlam : lam ∈ S) : LowerSemicontinuousOn (fun α => Hfun P f β x α lam) I := by
    let := mixture_isProbability P lam hlam
    exact (ru_continuous (mixture P lam) f β hβ1 x
      (mixture_integrable P (f x) hf lam)).lowerSemicontinuous.lowerSemicontinuousOn I
  have hcv (lam) (hlam : lam ∈ S) : ConvexOn ℝ I (fun α => Hfun P f β x α lam) := by
    let := mixture_isProbability P lam hlam
    exact (ru_convex (mixture P lam) f β hβ1 x
      (mixture_integrable P (f x) hf lam)).subset (Set.subset_univ I) (convex_Icc A B)
  have husc (α) (hα : α ∈ I) : UpperSemicontinuousOn (Hfun P f β x α) S :=
    (H_continuous_lam P f β hβ0 hβ1 x hf α).upperSemicontinuousOn
  obtain ⟨α,hα,lam,hlam,hs⟩ := Sion.exists_isSaddlePointOn hIne (convex_Icc A B)
    isCompact_Icc hlsc (fun z hz => (hcv z hz).quasiconvexOn)
    (convex_stdSimplex ℝ (Fin l)) hSne (isCompact_stdSimplex ℝ (Fin l)) husc
    (fun t ht => (H_concave_lam P f β hβ0 hβ1 x hf t).quasiconcaveOn)
  obtain ⟨r,hr,hm⟩ := (argmin_H_subset P f β hβ0 hβ1 x hf a b hab lam hlam).2
  have hαmin : IsMinOn (fun t => Hfun P f β x t lam) Set.univ α := by
    apply isMinOn_iff.mpr
    intro t ht
    exact (hs r hr lam hlam).trans (isMinOn_iff.mp hm t ht)
  exact ⟨α,hα,lam,hlam,hαmin,fun mu hmu => hs α hα mu hmu⟩
end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex
lemma inf_range_of_min (g : ℝ → ℝ) (q : ℝ) (hm : IsMinOn g Set.univ q) :
    sInf (Set.range g) = g q := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q,rfl⟩,?_⟩
  rintro y ⟨t,rfl⟩
  exact isMinOn_iff.mp hm t (Set.mem_univ t)

lemma saddle_values {l m n : ℕ} [NeZero l]
    (P : Fin l → Measure (Fin m → ℝ)) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i))
    (α : ℝ) (lam : Fin l → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin l))
    (hm : IsMinOn (fun t => Hfun P f β x t lam) Set.univ α)
    (hr : ∀ mu ∈ stdSimplex ℝ (Fin l), Hfun P f β x α mu ≤ Hfun P f β x α lam) :
    IsGreatest ((fun mu => cvar (mixture P mu) f β x) '' stdSimplex ℝ (Fin l))
      (Hfun P f β x α lam) ∧
    sSup ((fun mu => Hfun P f β x α mu) '' stdSimplex ℝ (Fin l)) = Hfun P f β x α lam ∧
    IsMinOn (fun t => sSup ((fun mu => Hfun P f β x t mu) '' stdSimplex ℝ (Fin l)))
      Set.univ α := by
  have he : cvar (mixture P lam) f β x = Hfun P f β x α lam := inf_range_of_min _ α hm
  have hv : IsGreatest ((fun mu => cvar (mixture P mu) f β x) '' stdSimplex ℝ (Fin l))
      (Hfun P f β x α lam) := by
    refine ⟨⟨lam,hlam,he⟩,?_⟩
    rintro y ⟨mu,hmu,rfl⟩
    let := mixture_isProbability P mu hmu
    obtain ⟨q,hq⟩ := ru_min_exists (mixture P mu) f β hβ0 hβ1 x (mixture_integrable P (f x) hf mu)
    have hval : cvar (mixture P mu) f β x = Hfun P f β x q mu := inf_range_of_min _ q hq
    change cvar (mixture P mu) f β x ≤ Hfun P f β x α lam
    rw [hval]
    exact (isMinOn_iff.mp hq α (Set.mem_univ α)).trans (hr mu hmu)
  have hs : sSup ((fun mu => Hfun P f β x α mu) '' stdSimplex ℝ (Fin l)) = Hfun P f β x α lam := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨lam,hlam,rfl⟩,by rintro y ⟨mu,hmu,rfl⟩; exact hr mu hmu⟩
  refine ⟨hv,hs,isMinOn_iff.mpr ?_⟩
  intro t ht
  rw [hs]
  have hb : BddAbove ((fun mu => Hfun P f β x t mu) '' stdSimplex ℝ (Fin l)) := by
    obtain ⟨mu,hmu,hmax⟩ := (H_continuous_lam P f β hβ0 hβ1 x hf t).upperSemicontinuousOn.exists_isMaxOn
      ⟨lam,hlam⟩ (isCompact_stdSimplex ℝ (Fin l))
    exact hmax.bddAbove
  exact (isMinOn_iff.mp hm t ht).trans (le_csSup hb ⟨lam,hlam,rfl⟩)
end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma simplex_average_le {l : ℕ} (v lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) (θ : ℝ) (hv : ∀ i, v i ≤ θ) :
    (∑ i, lam i*v i) ≤ θ := by
  calc
    _ ≤ ∑ i, lam i*θ := Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hv i) (h.1 i))
    _ = θ := by rw [← Finset.sum_mul,h.2,one_mul]

lemma simplex_average_maximum {l : ℕ} [NeZero l] (v : Fin l → ℝ) :
    sSup ((fun lam : Fin l → ℝ ↦ ∑ i, lam i*v i) '' stdSimplex ℝ (Fin l)) =
      Finset.univ.sup' Finset.univ_nonempty v := by
  let M := Finset.univ.sup' Finset.univ_nonempty v
  have hm : ∀ i, v i ≤ M := fun i ↦ Finset.le_sup' v (Finset.mem_univ i)
  have hb : BddAbove ((fun lam : Fin l → ℝ ↦ ∑ i, lam i*v i) '' stdSimplex ℝ (Fin l)) := by
    refine ⟨M,?_⟩
    rintro y ⟨lam,hlam,rfl⟩
    exact simplex_average_le v lam hlam M hm
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  have hp : (Pi.single i 1 : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l) := single_mem_stdSimplex ℝ i
  have hs : (∑ j, (Pi.single i 1 : Fin l → ℝ) j*v j) = v i := by simp [Pi.single_apply]
  apply le_antisymm
  · apply csSup_le ((show (stdSimplex ℝ (Fin l)).Nonempty from ⟨Pi.single i 1,hp⟩).image _)
    rintro y ⟨lam,hlam,rfl⟩
    exact simplex_average_le v lam hlam M hm
  · rw [he]
    rw [← hs]
    exact le_csSup hb ⟨Pi.single i 1,hp,rfl⟩

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

theorem eq_58_59 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    (∀ α θ : ℝ, (∀ lam ∈ stdSimplex ℝ (Fin l), ∑ i, lam i * Fi P f β x i α ≤ θ) ↔
        ∀ i, Fi P f β x i α ≤ θ) ∧
      ∀ α : ℝ, sSup ((fun lam => ∑ i, lam i * Fi P f β x i α) '' stdSimplex ℝ (Fin l)) =
        FL P f β x α := by
  constructor
  · intro α θ
    constructor
    · intro h i
      have hp : (Pi.single i 1 : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l) := single_mem_stdSimplex ℝ i
      simpa [Pi.single_apply] using h (Pi.single i 1) hp
    · intro h lam hlam
      exact simplex_average_le (fun i ↦ Fi P f β x i α) lam hlam θ h
  · intro α
    exact simplex_average_maximum (fun i ↦ Fi P f β x i α)


end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex
lemma component_intervals {l m n : ℕ}
    (P : Fin l → Measure (Fin m → ℝ)) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) :
    ∃ a b : Fin l → ℝ, ∀ i, {α : ℝ | IsMinOn (Fi P f β x i) Set.univ α} = Set.Icc (a i) (b i) := by
  have hi (i : Fin l) := argmin_interval_complete (P i) f β hβ0 hβ1 x (hf i)
  choose a b hle he using hi
  exact ⟨a,b,he⟩

theorem theorem_1 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∃ α₀ : ℝ, IsMinOn (FL P f β x) Set.univ α₀ ∧
      wcvar P f β x = FL P f β x α₀ := by
  obtain ⟨a,b,hab⟩ := component_intervals P f β hβ0 hβ1 x hf
  obtain ⟨α,hα,lam,hlam,hm,hr⟩ := common_saddle P f β hβ0 hβ1 x hf a b hab
  obtain ⟨hg,hs,hmin⟩ := saddle_values P f β hβ0 hβ1 x hf α lam hlam hm hr
  have hsup (t : ℝ) : sSup ((fun mu => Hfun P f β x t mu) '' stdSimplex ℝ (Fin l)) = FL P f β x t := by
    have he : (fun mu => Hfun P f β x t mu) '' stdSimplex ℝ (Fin l) =
        (fun mu => ∑ i, mu i * Fi P f β x i t) '' stdSimplex ℝ (Fin l) := by
      apply Set.image_congr
      intro mu hmu
      exact eq_53 P f β hβ0 hβ1 x hf mu hmu t
    rw [he]
    exact (eq_58_59 P f β hβ0 hβ1 x hf).2 t
  refine ⟨α,?_,?_⟩
  · simpa only [hsup] using hmin
  · unfold wcvar
    rw [hg.csSup_eq,← hs,hsup]
end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
theorem solution {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∃ α₀ : ℝ, IsMinOn (FL P f β x) Set.univ α₀ ∧ wcvar P f β x = FL P f β x α₀ := MixtureCodex.theorem_1 P f β hβ0 hβ1 x hf

end

#print axioms solution
