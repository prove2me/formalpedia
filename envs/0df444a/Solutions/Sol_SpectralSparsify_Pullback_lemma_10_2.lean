-- Prove2me | solution 1 for SpectralSparsify.Pullback.lemma_10_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T03:01:44.453653+00:00
-- url     : https://prove2.me/submissions/3544da6c-b58d-4761-8fa9-a5a6e32bb698

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

section

namespace SpectralSparsify.Pullback.PBFresh

open SpectralSparsify.Sampling

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V]

lemma lapForm_nonneg (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (x : V → ℝ) :
    0 ≤ lapForm w x := by
  unfold lapForm
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => mul_nonneg (hw u v) (sq_nonneg _))

lemma lapForm_add (w z : V → V → ℝ) (x : V → ℝ) :
    lapForm (w + z) x = lapForm w x + lapForm z x := by
  simp only [lapForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma lapForm_smul (a : ℝ) (w : V → V → ℝ) (x : V → ℝ) :
    lapForm (a • w) x = a * lapForm w x := by
  simp only [lapForm, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

lemma lapForm_mono (w z : V → V → ℝ) (h : ∀ u v, w u v ≤ z u v) (x : V → ℝ) :
    lapForm w x ≤ lapForm z x := by
  unfold lapForm
  gcongr with u v
  exact h u v

omit [Fintype V] in
lemma cross_add_intra {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) :
    crossPart w π + intraPart w π = w := by
  funext u v
  simp only [Pi.add_apply, crossPart, intraPart]
  split_ifs <;> simp

omit [Fintype V] in
lemma intra_nonneg {k : ℕ} {w : V → V → ℝ} (hw : IsWGraph w) (π : V → Fin k) :
    ∀ u v, 0 ≤ intraPart w π u v := by
  intro u v
  unfold intraPart
  split_ifs
  · exact hw.2.1 u v
  · rfl

omit [Fintype V] in
lemma cross_nonneg {k : ℕ} {w : V → V → ℝ} (hw : IsWGraph w) (π : V → Fin k) :
    ∀ u v, 0 ≤ crossPart w π u v := by
  intro u v
  unfold crossPart
  split_ifs
  · rfl
  · exact hw.2.1 u v

omit [Fintype V] in
lemma cross_symm {k : ℕ} {w : V → V → ℝ} (hw : IsWGraph w) (π : V → Fin k) :
    ∀ u v, crossPart w π u v = crossPart w π v u := by
  intro u v
  simp only [crossPart, eq_comm (a := π v) (b := π u), hw.1 u v]

omit [Fintype V] in
lemma intra_symm {k : ℕ} {w : V → V → ℝ} (hw : IsWGraph w) (π : V → Fin k) :
    ∀ u v, intraPart w π u v = intraPart w π v u := by
  intro u v
  simp only [intraPart, eq_comm (a := π v) (b := π u), hw.1 u v]

lemma lapForm_split {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) (x : V → ℝ) :
    lapForm w x = lapForm (crossPart w π) x + lapForm (intraPart w π) x := by
  rw [← lapForm_add, cross_add_intra]

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V] {k : ℕ}

lemma sum_fibers (π : V → Fin k) (f : V → ℝ) :
    ∑ i, ∑ u ∈ Finset.univ.filter (fun u => π u = i), f u = ∑ u, f u := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

lemma contraction_weighted_sum (w : V → V → ℝ) (π : V → Fin k)
    (F : Fin k → Fin k → ℝ) (hF : ∀ i, F i i = 0) :
    ∑ i, ∑ j, contraction w π i j * F i j = ∑ u, ∑ v, w u v * F (π u) (π v) := by
  classical
  have ht (i j : Fin k) : contraction w π i j * F i j =
      ∑ u ∈ Finset.univ.filter (fun u => π u = i),
        ∑ v ∈ Finset.univ.filter (fun v => π v = j), w u v * F (π u) (π v) := by
    by_cases hij : i = j
    · subst j
      simp only [contraction, ite_true, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2, hF, mul_zero]
    · simp only [contraction, hij, ite_false, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
  simp_rw [ht]
  calc
    _ = ∑ i, ∑ u ∈ Finset.univ.filter (fun u => π u = i),
        ∑ j, ∑ v ∈ Finset.univ.filter (fun v => π v = j), w u v * F (π u) (π v) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [sum_fibers]

lemma lapForm_contraction (w : V → V → ℝ) (π : V → Fin k) (y : Fin k → ℝ) :
    lapForm (contraction w π) y = lapForm w (fun u => y (π u)) := by
  unfold lapForm
  congr 1
  exact contraction_weighted_sum w π (fun i j => (y i - y j) ^ 2) (by simp)

lemma sum_contraction_eq (w : V → V → ℝ) (π : V → Fin k)
    (hc : ∀ u v, π u = π v → w u v = 0) :
    ∑ i, ∑ j, contraction w π i j = ∑ u, ∑ v, w u v := by
  classical
  have h := contraction_weighted_sum w π (fun i j => if i = j then 0 else 1) (by simp)
  have hl (i j : Fin k) : contraction w π i j * (if i = j then 0 else 1) =
      contraction w π i j := by
    by_cases hij : i = j
    · subst j; simp [contraction]
    · simp [hij]
  have hr (u v : V) : w u v * (if π u = π v then 0 else 1) = w u v := by
    by_cases huv : π u = π v
    · simp [huv, hc u v huv]
    · simp [huv]
  simpa only [hl, hr] using h

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V]

lemma sum_basis_sq [DecidableEq V] (u v : V) :
    ∑ i : V, ((if u = i then (1 : ℝ) else 0) - (if v = i then 1 else 0)) ^ 2 =
      if u = v then 0 else 2 := by
  classical
  by_cases huv : u = v
  · subst v; simp
  · have hi (i : V) : ((if u = i then (1 : ℝ) else 0) -
          (if v = i then 1 else 0)) ^ 2 =
          (if u = i then 1 else 0) + (if v = i then 1 else 0) := by
      by_cases hu : u = i <;> by_cases hv : v = i <;> simp_all
    simp only [hi, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      if_neg huv]
    norm_num

lemma sum_lapForm_basis [DecidableEq V] (w : V → V → ℝ) (hd : ∀ u, w u u = 0) :
    ∑ i : V, lapForm w (fun u => if u = i then 1 else 0) = ∑ u, ∑ v, w u v := by
  classical
  unfold lapForm
  rw [← Finset.mul_sum]
  calc
    _ = (1/2:ℝ) * ∑ u, ∑ v, ∑ i : V,
        w u v * ((if u = i then (1:ℝ) else 0) - (if v = i then 1 else 0))^2 := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = (1/2:ℝ) * ∑ u, ∑ v, w u v * (if u = v then 0 else 2) := by
      simp_rw [← Finset.mul_sum, sum_basis_sq]
    _ = _ := by
      have h (u v : V) : w u v * (if u = v then 0 else 2) = 2 * w u v := by
        by_cases huv : u = v
        · subst v; simp [hd]
        · simp [huv, mul_comm]
      simp_rw [h, ← Finset.mul_sum]
      ring

lemma approx_total_weight [DecidableEq V] {s : ℝ} (hs : 0 < s)
    {w z : V → V → ℝ} (hw : ∀ u, w u u = 0) (hz : ∀ u, z u u = 0)
    (ha : IsApprox s z w) :
    (1/2:ℝ) * (∑ u, ∑ v, z u v) ≤ s * ((1/2:ℝ) * (∑ u, ∑ v, w u v)) := by
  have h (i : V) : lapForm z (fun u => if u = i then 1 else 0) ≤
      s * lapForm w (fun u => if u = i then 1 else 0) := by
    have h := (ha (fun u => if u = i then 1 else 0)).1
    rw [mul_comm s]
    apply (div_le_iff₀ hs).mp
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset V)) => h i)
  rw [sum_lapForm_basis z hz] at hsum
  have hsum' : (∑ u, ∑ v, z u v) ≤ s * (∑ u, ∑ v, w u v) := by
    simpa only [← Finset.mul_sum, sum_lapForm_basis w hw] using hsum
  linarith

lemma cross_total_weight_le {k : ℕ} {w : V → V → ℝ} (_hw : IsWGraph w) (π : V → Fin k)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    (1/2:ℝ) * (∑ u, ∑ v, crossPart w π u v) ≤ (Fintype.card V : ℝ)^2/2 := by
  have h (u v : V) : crossPart w π u v ≤ 1 := by
    unfold crossPart
    split_ifs with hp
    · norm_num
    · by_cases hz : w u v = 0
      · simp [hz]
      · rw [h3 u v hp hz]
  have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) =>
    Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => h u v))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  nlinarith

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

omit [DecidableEq V] in
lemma cross_total_weight_three_quarters {w : V → V → ℝ} (hw : IsWGraph w)
    (π : V → Fin k) (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    (1/2:ℝ) * (∑ u, ∑ v, crossPart w π u v) ≤ 3*(Fintype.card V : ℝ)^2/4 := by
  have h := cross_total_weight_le hw π h3
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

omit [DecidableEq V] in
lemma pullback_total_weight_three_quarters {w : V → V → ℝ} (hw : IsWGraph w)
    (π : V → Fin k) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1/2)
    (zt : Fin k → Fin k → ℝ) (hzt : IsWGraph zt)
    (ha : IsApprox (1+ε) zt (contraction (crossPart w π) π))
    (wt : V → V → ℝ) (hpb : IsPullback wt zt π)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    (1/2:ℝ) * (∑ u, ∑ v, wt u v) ≤ 3*(Fintype.card V : ℝ)^2/4 := by
  have hs : 0 < 1+ε := by linarith
  have h := approx_total_weight hs (w := contraction (crossPart w π) π)
    (z := zt) (by intro i; simp [contraction]) hzt.2.2 ha
  rw [← hpb.2.1, sum_contraction_eq wt π hpb.1] at h
  have hc : ∀ u v, π u = π v → crossPart w π u v = 0 := by
    intro u v huv; simp [crossPart, huv]
  rw [sum_contraction_eq (crossPart w π) π hc] at h
  have hb := mul_le_mul_of_nonneg_left (cross_total_weight_le hw π h3) hs.le
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V] {k : ℕ}

lemma relocation_error_energy (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v)
    (π : V → Fin k) (hcross : ∀ u v, π u = π v → w u v = 0)
    (c E : ℝ) (hc : 0 < c) (hE : 0 ≤ E) (hn : 0 < Fintype.card V)
    (z : V → ℝ)
    (hmass : (1/2:ℝ)*(∑ u, ∑ v, w u v) ≤ 3*(Fintype.card V : ℝ)^2/4)
    (hd : ∀ u v, π u ≠ π v → c^2*(Fintype.card V : ℝ)^2*(z u-z v)^2 ≤ E) :
    lapForm w z ≤ 3*E/(4*c^2) := by
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hden : 0 < c^2*(Fintype.card V : ℝ)^2 := by positivity
  have hpt (u v : V) : w u v * (z u-z v)^2 ≤
      w u v * (E/(c^2*(Fintype.card V : ℝ)^2)) := by
    by_cases hsame : π u = π v
    · rw [hcross u v hsame]; simp
    · apply mul_le_mul_of_nonneg_left _ (hw u v)
      apply (le_div_iff₀ hden).mpr
      nlinarith [hd u v hsame]
  calc
    lapForm w z ≤ (1/2:ℝ) * ∑ u, ∑ v,
        w u v * (E/(c^2*(Fintype.card V : ℝ)^2)) := by
      unfold lapForm
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpt u v) (by norm_num)
    _ = ((1/2:ℝ)*(∑ u, ∑ v, w u v)) * (E/(c^2*(Fintype.card V : ℝ)^2)) := by
      simp only [← Finset.sum_mul]
      ring
    _ ≤ (3*(Fintype.card V : ℝ)^2/4) * (E/(c^2*(Fintype.card V : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right hmass (div_nonneg hE hden.le)
    _ = 3*E/(4*c^2) := by
      field_simp [ne_of_gt hc, ne_of_gt hn0]

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh

lemma young_relocation (c : ℝ) (hc : 0 < c) (a b : ℝ) :
    a^2 ≤ (1+1/c)*b^2 + (1+c)*(a-b)^2 := by
  have hid : (1+1/c)*b^2 + (1+c)*(a-b)^2 - a^2 =
      (c*(a-b)-b)^2/c := by
    field_simp
    ring
  have h := div_nonneg (sq_nonneg (c*(a-b)-b)) hc.le
  rw [← hid] at h
  linarith

lemma relocation_absorption (c : ℝ) (hc : 3 ≤ c) :
    (1+c)*3/(4*c^2) ≤ 1/c := by
  have hc0 : 0 < c := by linarith
  apply (div_le_div_iff₀ (by positivity : 0 < 4*c^2) hc0).mpr
  nlinarith

lemma energy_transfer (c E Fx Fy err : ℝ) (hc : 3 ≤ c) (hE : 0 ≤ E)
    (herr : err ≤ 3*E/(4*c^2))
    (hyoung : Fx ≤ (1+1/c)*Fy + (1+c)*err) :
    Fx+E ≤ (1+1/c)*(Fy+E) := by
  have hc0 : 0 < c := by linarith
  have he := mul_le_mul_of_nonneg_left herr (show 0 ≤ 1+c by linarith)
  have ha := mul_le_mul_of_nonneg_right (relocation_absorption c hc) hE
  have hid : (1+c)*(3*E/(4*c^2)) = ((1+c)*3/(4*c^2))*E := by ring
  rw [hid] at he
  nlinarith

lemma energy_three_factor (a b X Y Z W : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hXY : X ≤ a*Y) (hYZ : Y ≤ b*Z) (hZW : Z ≤ a*W) :
    X ≤ (b*a^2)*W := by
  calc
    X ≤ a*Y := hXY
    _ ≤ a*(b*Z) := mul_le_mul_of_nonneg_left hYZ ha
    _ ≤ a*(b*(a*W)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hZW hb) ha
    _ = _ := by ring

lemma add_common_energy_factor (s A B E : ℝ) (hs : 1 ≤ s) (hE : 0 ≤ E)
    (hAB : A ≤ s*B) : A+E ≤ s*(B+E) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hE]

end SpectralSparsify.Pullback.PBFresh
end

section

open scoped BigOperators
open SpectralSparsify.Sampling
namespace SpectralSparsify.Pullback.PBFresh
variable {V : Type*} [Fintype V]

lemma lapForm_young (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (x y : V → ℝ) (c : ℝ) (hc : 0 < c) :
    lapForm w x ≤ (1+1/c)*lapForm w y + (1+c)*lapForm w (x-y) := by
  have hp (i j : V) : w i j*(x i-x j)^2 ≤
      (1+1/c)*(w i j*(y i-y j)^2) +
      (1+c)*(w i j*((x-y) i-(x-y) j)^2) := by
    have h := mul_le_mul_of_nonneg_left (young_relocation c hc (x i-x j) (y i-y j)) (hw i j)
    have hid : (x i-x j)-(y i-y j) = (x-y) i-(x-y) j := by
      simp only [Pi.sub_apply]
      ring
    rw [hid] at h
    calc
      _ ≤ w i j*((1+1/c)*(y i-y j)^2+(1+c)*((x-y) i-(x-y) j)^2) := h
      _ = _ := by ring
  calc
    lapForm w x ≤ (1/2:ℝ) * ((1+1/c)*(∑ i, ∑ j, w i j*(y i-y j)^2) +
        (1+c)*(∑ i, ∑ j, w i j*((x-y) i-(x-y) j)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = _ := by unfold lapForm; ring

lemma lapForm_sub_comm (w : V → V → ℝ) (x y : V → ℝ) :
    lapForm w (y-x) = lapForm w (x-y) := by
  unfold lapForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

lemma energy_transfer_forms (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (x y : V → ℝ) (E c : ℝ) (hE : 0 ≤ E) (hc : 3 ≤ c)
    (herr : lapForm w (x-y) ≤ 3*E/(4*c^2)) :
    lapForm w x + E ≤ (1+1/c)*(lapForm w y+E) ∧
      lapForm w y + E ≤ (1+1/c)*(lapForm w x+E) := by
  have hc0 : 0 < c := by linarith
  constructor
  · exact energy_transfer c E _ _ _ hc hE herr (lapForm_young w hw x y c hc0)
  · have hr : lapForm w (y-x) ≤ 3*E/(4*c^2) := by
      rw [lapForm_sub_comm]
      exact herr
    exact energy_transfer c E _ _ _ hc hE hr (lapForm_young w hw y x c hc0)

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

variable {V : Type*} [Fintype V] {k : ℕ}

lemma representative_comparison (w0 : V → V → ℝ) (hw0 : ∀ u v, 0 ≤ w0 u v)
    (π : V → Fin k) (hcross : ∀ u v, π u = π v → w0 u v = 0)
    (r : Fin k → V) (x : V → ℝ) (c E : ℝ) (hc : 3 ≤ c) (hE : 0 ≤ E)
    (hn : 0 < Fintype.card V)
    (hmass : (1/2:ℝ)*(∑ u, ∑ v, w0 u v) ≤ 3*(Fintype.card V : ℝ)^2/4)
    (hd : ∀ u v, π u ≠ π v → c^2*(Fintype.card V : ℝ)^2 *
      ((x u-x (r (π u)))-(x v-x (r (π v))))^2 ≤ E) :
    lapForm w0 x+E ≤ (1+1/c)*(lapForm w0 (fun u => x (r (π u)))+E) ∧
    lapForm w0 (fun u => x (r (π u)))+E ≤ (1+1/c)*(lapForm w0 x+E) := by
  have hc0 : 0 < c := by linarith
  apply energy_transfer_forms w0 hw0 x (fun u => x (r (π u))) E c hE hc
  apply relocation_error_energy w0 hw0 π hcross c E hc0 hE hn _ hmass
  intro u v huv
  simpa only [Pi.sub_apply] using hd u v huv

end SpectralSparsify.Pullback.PBFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Pullback.PBFresh

lemma dart_double_nodup {V : Type*} {G : SimpleGraph V} (L : List G.Dart)
    (hL : (L.map SimpleGraph.Dart.edge).Nodup) :
    (L ++ L.map SimpleGraph.Dart.symm).Nodup := by
  have hn : L.Nodup := List.Nodup.of_map _ hL
  rw [List.nodup_append]
  refine ⟨hn, hn.map SimpleGraph.Dart.symm_involutive.injective, ?_⟩
  apply List.disjoint_iff_ne.mp
  apply List.disjoint_left.mpr
  intro d hd hd'
  obtain ⟨e, he, hde⟩ := List.mem_map.mp hd'
  have hh : d = e := List.inj_on_of_nodup_map hL hd he (by rw [← hde]; simp)
  exact e.symm_ne (hde.trans hh)

lemma list_sum_le_univ {A : Type*} [Fintype A] (L : List A) (hL : L.Nodup)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) : (L.map f).sum ≤ ∑ a, f a := by
  classical
  rw [← List.sum_toFinset f hL]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => hf a)

lemma dart_energy_le_half_sum {V : Type*} [Fintype V] {G : SimpleGraph V}
    (L : List G.Dart) (hL : (L.map SimpleGraph.Dart.edge).Nodup)
    (F : V → V → ℝ) (hF : ∀ u v, 0 ≤ F u v) (hsym : ∀ u v, F u v = F v u) :
    (L.map (fun d => F d.fst d.snd)).sum ≤ (1 / 2 : ℝ) * ∑ u, ∑ v, F u v := by
  classical
  let K := (L ++ L.map SimpleGraph.Dart.symm).map SimpleGraph.Dart.toProd
  have hK : K.Nodup := (dart_double_nodup L hL).map SimpleGraph.Dart.toProd_injective
  have hb := list_sum_le_univ K hK (fun p => F p.1 p.2) (fun p => hF p.1 p.2)
  have he : (K.map (fun p => F p.1 p.2)).sum =
      2 * (L.map (fun d => F d.fst d.snd)).sum := by
    simp only [K, List.map_append, List.map_map, List.sum_append, Function.comp_def,
      SimpleGraph.Dart.symm, Prod.fst_swap, Prod.snd_swap]
    rw [show (L.map (fun d => F d.snd d.fst)) = L.map (fun d => F d.fst d.snd) from
      List.map_congr_left (fun d _ => hsym d.snd d.fst)]
    ring
  rw [he, Fintype.sum_prod_type] at hb
  linarith

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh

lemma intra_adj_data {V : Type*} {k : ℕ} (w : V → V → ℝ)
    (hw : SpectralSparsify.Sampling.IsWGraph w) (pi : V → Fin k) {u v : V}
    (h : (intraGraph w pi).Adj u v) : pi u = pi v ∧ w u v ≠ 0 := by
  rcases h.2 with h | h
  · exact h
  · exact ⟨h.1.symm, by rw [hw.1 u v]; exact h.2⟩

lemma walk_fiber {V I : Type*} {G : SimpleGraph V} (pi : V → I)
    (hG : ∀ a b, G.Adj a b → pi a = pi b) {u v : V} (p : G.Walk u v) :
    ∀ z ∈ p.support, pi z = pi u := by
  induction p with
  | @nil a =>
    intro z hz
    have he : z = a := by simpa using hz
    rw [he]
  | @cons a b c hab p ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · rfl
    · exact (ih z hz).trans (hG a b hab).symm

lemma disjoint_fiber_supports {V I : Type*} {G : SimpleGraph V} (pi : V → I)
    (hG : ∀ a b, G.Adj a b → pi a = pi b) {u u' v v' : V}
    (p : G.Walk u u') (q : G.Walk v v') (huv : pi u ≠ pi v) :
    List.Disjoint p.support q.support := by
  apply List.disjoint_left.mpr
  intro z hp hq
  exact huv ((walk_fiber pi hG p z hp).symm.trans (walk_fiber pi hG q z hq))

lemma joint_path_length_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u u' v v' : V} (p : G.Walk u u') (q : G.Walk v v')
    (hp : p.IsPath) (hq : q.IsPath) (hd : List.Disjoint p.support q.support) :
    p.length + q.length ≤ Fintype.card V := by
  have hn : (p.support ++ q.support).Nodup := List.nodup_append.mpr
    ⟨hp.support_nodup, hq.support_nodup, List.disjoint_iff_ne.mp hd⟩
  have hh := hn.length_le_card
  rw [List.length_append, p.length_support, q.length_support] at hh
  omega

lemma disjoint_supports_edges {V : Type*} {G : SimpleGraph V}
    {u u' v v' : V} (p : G.Walk u u') (q : G.Walk v v')
    (hd : List.Disjoint p.support q.support) : List.Disjoint p.edges q.edges := by
  apply List.disjoint_left.mpr
  intro e he hf
  obtain ⟨d, hdp, rfl⟩ := List.mem_map.mp he
  have hp := p.dart_fst_mem_support_of_mem_darts hdp
  have hq : d.fst ∈ q.support := SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨d.edge, hf, by simp [SimpleGraph.Dart.edge]⟩)
  exact List.disjoint_left.mp hd hp hq

lemma joint_darts_edges_nodup {V : Type*} {G : SimpleGraph V}
    {u u' v v' : V} (p : G.Walk u u') (q : G.Walk v v')
    (hp : p.IsPath) (hq : q.IsPath) (hd : List.Disjoint p.support q.support) :
    ((p.darts ++ q.darts).map SimpleGraph.Dart.edge).Nodup := by
  rw [List.map_append]
  exact List.nodup_append.mpr ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup,
    List.disjoint_iff_ne.mp (disjoint_supports_edges p q hd)⟩

end SpectralSparsify.Pullback.PBFresh
end

section

open scoped BigOperators
open SpectralSparsify.Sampling
namespace SpectralSparsify.Pullback.PBFresh

lemma path_list_heavy_energy {V : Type*} [Fintype V] {k : ℕ}
    (w : V → V → ℝ) (hw : IsWGraph w) (pi : V → Fin k) (c : ℝ)
    (h2 : ∀ u v, pi u = pi v → w u v ≠ 0 → c^2 * (Fintype.card V : ℝ)^3 ≤ w u v)
    (x : V → ℝ) (L : List (intraGraph w pi).Dart)
    (hL : (L.map SimpleGraph.Dart.edge).Nodup) :
    c^2 * (Fintype.card V : ℝ)^3 *
      (L.map (fun d => (x d.fst - x d.snd)^2)).sum ≤ lapForm (intraPart w pi) x := by
  classical
  let F := fun u v => intraPart w pi u v * (x u - x v)^2
  have hF (u v : V) : 0 ≤ F u v := by
    dsimp [F, intraPart]
    split_ifs
    · exact mul_nonneg (hw.2.1 u v) (sq_nonneg _)
    · simp
  have hsym (u v : V) : F u v = F v u := by
    by_cases h : pi u = pi v
    · dsimp only [F, intraPart]
      rw [if_pos h, if_pos h.symm, hw.1 u v]
      ring
    · simp only [F, intraPart, h, Ne.symm h, if_false, zero_mul]
  have hb := dart_energy_le_half_sum L hL F hF hsym
  have he : c^2 * (Fintype.card V : ℝ)^3 *
      (L.map (fun d => (x d.fst - x d.snd)^2)).sum ≤
        (L.map (fun d => F d.fst d.snd)).sum := by
    rw [← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro d _
    have hd := intra_adj_data w hw pi d.adj
    dsimp [F]
    rw [intraPart, if_pos hd.1]
    exact mul_le_mul_of_nonneg_right (h2 d.fst d.snd hd.1 hd.2) (sq_nonneg _)
  exact he.trans hb

end SpectralSparsify.Pullback.PBFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Pullback.PBFresh

lemma list_cauchy (L : List ℝ) : L.sum ^ 2 ≤ (L.length : ℝ) * (L.map (fun a => a^2)).sum := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin L.length))
    (fun _ => (1 : ℝ)) (fun i => L[i.val])
  have he : (∑ i : Fin L.length, L[i.val]) = L.sum := by
    rw [← List.sum_ofFn, List.ofFn_getElem]
  have he2 : (∑ i : Fin L.length, L[i.val] ^ 2) = (L.map (fun a => a^2)).sum := by
    calc
      _ = ((List.ofFn (fun i : Fin L.length => L[i.val])).map (fun a => a^2)).sum := by
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
      _ = _ := by rw [List.ofFn_getElem]
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, he, he2] using h

lemma walk_telescope {V : Type*} {G : SimpleGraph V} (x : V → ℝ)
    {u v : V} (p : G.Walk u v) :
    (p.darts.map (fun d => x d.fst - x d.snd)).sum = x u - x v := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    ring

lemma joint_walk_cauchy {V : Type*} {G : SimpleGraph V} (x : V → ℝ)
    {u u' v v' : V} (p : G.Walk u u') (q : G.Walk v v') :
    ((x u - x u') + (x v - x v'))^2 ≤
      ((p.length + q.length : ℕ) : ℝ) *
        ((p.darts ++ q.darts).map (fun d => (x d.fst - x d.snd)^2)).sum := by
  have h := list_cauchy ((p.darts ++ q.darts).map (fun d => x d.fst - x d.snd))
  simpa only [List.map_append, List.sum_append, walk_telescope, List.length_append,
    List.length_map, SimpleGraph.Walk.length_darts, List.map_map, Function.comp_def] using h

end SpectralSparsify.Pullback.PBFresh
end

section

open SpectralSparsify.Sampling
namespace SpectralSparsify.Pullback.PBFresh

lemma relocation_sq_bound {V : Type*} [Fintype V] {k : ℕ}
    (w : V → V → ℝ) (hw : IsWGraph w) (pi : V → Fin k) (c : ℝ)
    (h1 : ∀ u v, pi u = pi v → (intraGraph w pi).Reachable u v)
    (h2 : ∀ u v, pi u = pi v → w u v ≠ 0 → c^2 * (Fintype.card V : ℝ)^3 ≤ w u v)
    (r : Fin k → V) (hr : ∀ i, pi (r i) = i) (x : V → ℝ)
    (u v : V) (huv : pi u ≠ pi v) :
    c^2 * (Fintype.card V : ℝ)^2 *
      ((x u - x (r (pi u))) - (x v - x (r (pi v))))^2 ≤
        lapForm (intraPart w pi) x := by
  classical
  obtain ⟨p, hp⟩ := (h1 u (r (pi u)) (hr _).symm).exists_isPath
  obtain ⟨q, hq⟩ := (h1 (r (pi v)) v (hr _)).exists_isPath
  have hG (a b : V) (h : (intraGraph w pi).Adj a b) : pi a = pi b :=
    (intra_adj_data w hw pi h).1
  have hd := disjoint_fiber_supports pi hG p q (by simpa only [hr] using huv)
  have hlen := joint_path_length_le p q hp hq hd
  have he := path_list_heavy_energy w hw pi c h2 x (p.darts ++ q.darts)
    (joint_darts_edges_nodup p q hp hq hd)
  have hcs := joint_walk_cauchy x p q
  let S := ((p.darts ++ q.darts).map (fun d => (x d.fst - x d.snd)^2)).sum
  have hS : 0 ≤ S := List.sum_nonneg (by
    intro a ha
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
    exact sq_nonneg _)
  have hcs' : ((x u - x (r (pi u))) - (x v - x (r (pi v))))^2 ≤
      (Fintype.card V : ℝ) * S := by
    have hlenR : ((p.length + q.length : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hlen
    convert hcs.trans (mul_le_mul_of_nonneg_right hlenR hS) using 1 <;> first | rfl | ring
  calc
    _ ≤ c^2 * (Fintype.card V : ℝ)^2 * ((Fintype.card V : ℝ) * S) :=
      mul_le_mul_of_nonneg_left hcs' (by positivity)
    _ = c^2 * (Fintype.card V : ℝ)^3 * S := by ring
    _ ≤ _ := he

end SpectralSparsify.Pullback.PBFresh
end

section

namespace SpectralSparsify.Pullback.PBFresh
open SpectralSparsify.Sampling

theorem pullback_theorem {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (hπ : Function.Surjective π)
    (ε c : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hc : 3 ≤ c)
    (zt : Fin k → Fin k → ℝ) (hzt : SpectralSparsify.Sampling.IsWGraph zt)
    (happrox : SpectralSparsify.Sampling.IsApprox (1 + ε) zt (contraction (crossPart w π) π))
    (wt : V → V → ℝ) (hwt : SpectralSparsify.Sampling.IsWGraph wt) (hpb : IsPullback wt zt π)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    SpectralSparsify.Sampling.IsApprox ((1 + ε) * (1 + 1 / c) ^ 2) (wt + intraPart w π) w := by
  classical
  by_cases hn : Fintype.card V = 0
  · let : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    intro x
    simp [lapForm]
  have hnpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hn
  let r : Fin k → V := fun i => Classical.choose (hπ i)
  have hr : ∀ i, π (r i) = i := fun i => Classical.choose_spec (hπ i)
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < 1+1/c := by positivity
  have hb0 : 0 < 1+ε := by linarith
  have hs0 : 0 < (1+ε)*(1+1/c)^2 := by positivity
  have hcross : ∀ u v, π u = π v → crossPart w π u v = 0 := by
    intro u v huv
    simp [crossPart, huv]
  intro x
  let E := lapForm (intraPart w π) x
  let y : V → ℝ := fun u => x (r (π u))
  have hE : 0 ≤ E := lapForm_nonneg _ (intra_nonneg hw π) x
  have hd := relocation_sq_bound w hw π c h1 h2 r hr x
  have hleft := representative_comparison (crossPart w π) (cross_nonneg hw π) π hcross
    r x c E hc hE hnpos (cross_total_weight_three_quarters hw π h3) hd
  have hright := representative_comparison wt hwt.2.1 π hpb.1 r x c E hc hE hnpos
    (pullback_total_weight_three_quarters hw π ε hε0 hε zt hzt happrox wt hpb h3) hd
  have hm := happrox (fun i => x (r i))
  rw [lapForm_contraction] at hm
  have hztform : lapForm zt (fun i => x (r i)) = lapForm wt y := by
    rw [← hpb.2.1, lapForm_contraction]
  rw [hztform] at hm
  change (1/(1+ε))*lapForm wt y ≤ lapForm (crossPart w π) y ∧
    lapForm (crossPart w π) y ≤ (1+ε)*lapForm wt y at hm
  have hmrev : lapForm wt y ≤ (1+ε)*lapForm (crossPart w π) y := by
    rw [mul_comm (1+ε)]
    apply (div_le_iff₀ hb0).mp
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hm.1
  have hmiddle := add_common_energy_factor (1+ε) _ _ E (by linarith) hE hm.2
  have hmiddlerev := add_common_energy_factor (1+ε) _ _ E (by linarith) hE hmrev
  have hupper := energy_three_factor (1+1/c) (1+ε) _ _ _ _ ha0.le hb0.le
    hleft.1 hmiddle hright.2
  have hlower := energy_three_factor (1+1/c) (1+ε) _ _ _ _ ha0.le hb0.le
    hright.1 hmiddlerev hleft.2
  have hsum : lapForm w x = lapForm (crossPart w π) x + E := lapForm_split w π x
  have htsum : lapForm (wt + intraPart w π) x = lapForm wt x + E := lapForm_add wt _ x
  rw [hsum, htsum]
  constructor
  · have hdiv : (lapForm wt x+E)/((1+ε)*(1+1/c)^2) ≤
        lapForm (crossPart w π) x+E := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith [hlower]
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hdiv
  · exact hupper

end SpectralSparsify.Pullback.PBFresh
end

open SpectralSparsify.Pullback

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (hπ : Function.Surjective π)
    (ε c : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hc : 3 ≤ c)
    (zt : Fin k → Fin k → ℝ) (hzt : SpectralSparsify.Sampling.IsWGraph zt)
    (happrox : SpectralSparsify.Sampling.IsApprox (1 + ε) zt (contraction (crossPart w π) π))
    (wt : V → V → ℝ) (hwt : SpectralSparsify.Sampling.IsWGraph wt) (hpb : IsPullback wt zt π)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    SpectralSparsify.Sampling.IsApprox ((1 + ε) * (1 + 1 / c) ^ 2) (wt + intraPart w π) w := by
  exact PBFresh.pullback_theorem w hw π hπ ε c hε0 hε hc zt hzt happrox wt hwt hpb h1 h2 h3
