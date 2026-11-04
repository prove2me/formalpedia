-- Prove2me | solution 1 for SONATA.Push.phi_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:51:36.788305+00:00
-- url     : https://prove2.me/submissions/d2fe76c8-a9d6-4c5a-ac6c-b50521a65916

import Mathlib
import Definitions.Def_SONATA_Push_Network

open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem hess_symm {d : ℕ} (φ : E d → ℝ) (x : E d)
    (hd : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ y)
    (hg : DifferentiableAt ℝ (gradient φ) x) (u v : E d) :
    ⟪hess φ x u, v⟫ = ⟪hess φ x v, u⟫ := by
  have key : (fun y => fderiv ℝ φ y) =
      fun y => (innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ) (gradient φ y) := by
    funext y; ext w; simp [gradient, InnerProductSpace.toDual_symm_apply]
  have h1 : ∀ᶠ y in nhds x, HasFDerivAt φ (fderiv ℝ φ y) y :=
    hd.mono fun y hy => hy.hasFDerivAt
  have h2 : HasFDerivAt (fun y => fderiv ℝ φ y)
      ((innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ).comp (hess φ x)) x := by
    rw [key]; exact (innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ).hasFDerivAt.comp x hg.hasFDerivAt
  have := second_derivative_symmetric_of_eventually h1 h2 u v
  simpa [hess] using this

theorem norm_apply_le_of_quad {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (hsym : ∀ u v, ⟪A u, v⟫ = ⟪A v, u⟫) (D : ℝ)
    (h : ∀ w, |⟪A w, w⟫| ≤ D * ‖w‖ ^ 2) (u : V) : ‖A u‖ ≤ D * ‖u‖ := by
  have key : ∀ s : ℝ, 2 * s * ‖A u‖ ^ 2 ≤ D * (‖u‖ ^ 2 + s ^ 2 * ‖A u‖ ^ 2) := by
    intro s
    set v := s • A u with hv
    have hp := abs_le.mp (h (u + v))
    have hm := abs_le.mp (h (u - v))
    have e1 : ⟪A (u + v), u + v⟫ - ⟪A (u - v), u - v⟫ = 4 * ⟪A u, v⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hsym v u]; ring
    have e2 : ⟪A u, v⟫ = s * ‖A u‖ ^ 2 := by
      rw [hv, inner_smul_right, real_inner_self_eq_norm_sq]
    have e3 : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      have := parallelogram_law_with_norm ℝ u v
      nlinarith [this]
    have e4 : ‖v‖ ^ 2 = s ^ 2 * ‖A u‖ ^ 2 := by
      rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have e5 : D * ‖u + v‖ ^ 2 + D * ‖u - v‖ ^ 2 = 2 * D * (‖u‖ ^ 2 + s ^ 2 * ‖A u‖ ^ 2) := by
      rw [← mul_add, e3, e4]; ring
    linarith [hp.2, hm.1]
  rcases eq_or_lt_of_le (norm_nonneg (A u)) with h0 | hpos
  · rw [← h0]
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have := (abs_nonneg _).trans (h u)
      have hD : 0 ≤ D := by
        by_contra hc; push Not at hc
        have : D * ‖u‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
        linarith
      positivity
  · have hu : 0 < ‖u‖ := by
      rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
      · have : u = 0 := norm_eq_zero.mp hu.symm
        simp [this] at hpos
      · exact hu
    have k := key (‖u‖ / ‖A u‖)
    have e : (‖u‖ / ‖A u‖) ^ 2 * ‖A u‖ ^ 2 = ‖u‖ ^ 2 := by
      field_simp
    have e' : 2 * (‖u‖ / ‖A u‖) * ‖A u‖ ^ 2 = 2 * ‖u‖ * ‖A u‖ := by
      field_simp
    rw [e, e'] at k
    nlinarith

theorem gradient_Fsum {m d : ℕ} (f : Fin m → E d → ℝ) (z : E d)
    (h : ∀ j, DifferentiableAt ℝ (f j) z) :
    gradient (Fsum f) z = (1 / (m : ℝ)) • ∑ j, gradient (f j) z := by
  have hF : HasFDerivAt (Fsum f) ((1 / (m : ℝ)) • ∑ j, fderiv ℝ (f j) z) z := by
    have hs : HasFDerivAt (fun x => ∑ j, f j x) (∑ j, fderiv ℝ (f j) z) z :=
      HasFDerivAt.fun_sum (fun j _ => (h j).hasFDerivAt)
    have := hs.const_mul (1 / (m : ℝ))
    exact this
  rw [gradient, hF.fderiv]
  simp [gradient, map_sum]

/-- Network facts: nonnegativity of the weights. -/
theorem C_nonneg {m : ℕ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl : ℝ} (hN : NetworkHyp Edges B C cl) :
    ∀ ν i j, 0 ≤ C ν i j := by
  obtain ⟨_, hcl, hdiag, hoff, _⟩ := hN
  intro ν i j
  by_cases hij : i = j
  · subst hij; linarith [hdiag ν i]
  · by_cases he : Edges ν j i
    · linarith [((hoff ν i j hij).1 he)]
    · rw [(hoff ν i j hij).2 he]

theorem phi_pos {m d : ℕ} {K : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν i, 0 < φ ν i := by
  obtain ⟨_, _, hφ0, _, hφs, _, _⟩ := hrun
  have hC := C_nonneg hN
  have hdiag := hN.2.2.1
  have hcl := hN.2.1
  intro ν
  induction ν with
  | zero => intro i; rw [hφ0 i]; norm_num
  | succ n ih =>
    intro i
    rw [hφs n i]
    have hle : C n i i * φ n i ≤ ∑ j, C n i j * φ n j :=
      Finset.single_le_sum (f := fun j => C n i j * φ n j)
        (fun j _ => mul_nonneg (hC n i j) (ih j).le) (Finset.mem_univ i)
    have : 0 < C n i i * φ n i := mul_pos (lt_of_lt_of_le hcl (hdiag n i)) (ih i)
    linarith

theorem phi_sum {m d : ℕ} {K : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν, ∑ i, φ ν i = m := by
  obtain ⟨_, _, hφ0, _, hφs, _, _⟩ := hrun
  have hcol := hN.2.2.2.2
  intro ν
  induction ν with
  | zero => simp [hφ0]
  | succ n ih =>
    simp_rw [hφs n]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol n, one_mul]
    exact ih

theorem x_mem {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L)
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν i, x ν i ∈ K := by
  have hpos := phi_pos hN hrun
  have hC := C_nonneg hN
  obtain ⟨hx0, _, _, hxh, hφs, hxs, _⟩ := hrun
  have hKcv : Convex ℝ K := hA.2.2.1
  intro ν
  induction ν with
  | zero => exact hx0
  | succ n ih =>
    intro i
    have hhalf : ∀ j, xhalf α x xh n j ∈ K := by
      intro j
      exact hKcv.add_smul_sub_mem (ih j) (hxh n j).1 ⟨hα0.le, hα1⟩
    rw [hxs n i, Finset.smul_sum]
    simp_rw [smul_smul]
    apply hKcv.sum_mem
    · intro j _
      exact mul_nonneg (inv_nonneg.mpr (hpos (n + 1) i).le) (mul_nonneg (hC n i j) (hpos n j).le)
    · rw [← Finset.mul_sum, ← hφs n i]
      exact inv_mul_cancel₀ (hpos (n + 1) i).ne'
    · intro j _; exact hhalf j

theorem grad_lip {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {μi Li : Fin m → ℝ} (h1 : HessBounds K f μi Li)
    (j : Fin m) {a b : E d} (ha : a ∈ K) (hb : b ∈ K) :
    ‖gradient (f j) a - gradient (f j) b‖ ≤ Li j * ‖a - b‖ := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _⟩ := hA
  have hdiffAt : ∀ z ∈ O, DifferentiableAt ℝ (f j) z :=
    fun z hz => ((hfi j).1 z hz).differentiableAt (hO.mem_nhds hz)
  have hgAt : ∀ z ∈ O, DifferentiableAt ℝ (gradient (f j)) z :=
    fun z hz => ((hfi j).2.1 z hz).differentiableAt (hO.mem_nhds hz)
  have hder : ∀ z ∈ K, HasFDerivWithinAt (gradient (f j)) (hess (f j) z) K z :=
    fun z hz => (hgAt z (hKO hz)).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ z ∈ K, ‖hess (f j) z‖ ≤ Li j := by
    intro z hz
    obtain ⟨_, hLj, hq⟩ := h1 j
    apply ContinuousLinearMap.opNorm_le_bound _ hLj.le
    intro u
    apply norm_apply_le_of_quad
    · intro u v
      apply hess_symm
      · exact Filter.mem_of_superset (hO.mem_nhds (hKO hz)) fun y hy => hdiffAt y hy
      · exact hgAt z (hKO hz)
    · intro w
      obtain ⟨hlo, hhi⟩ := hq z hz w
      have : 0 ≤ μi j * ‖w‖ ^ 2 := mul_nonneg (h1 j).1 (sq_nonneg _)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖w‖]
  exact hKcv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hb ha

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem cross {α : Type*} (r : α → α → Prop) (S : α → Prop) {a c : α}
    (h : Relation.ReflTransGen r a c) (ha : S a) (hc : ¬ S c) :
    ∃ x y, S x ∧ ¬ S y ∧ r x y := by
  revert hc
  induction h with
  | refl => intro hc; exact absurd ha hc
  | @tail b c' _ hbc ih =>
    intro hc
    by_cases hb : S b
    · exact ⟨_, _, hb, hc, hbc⟩
    · exact ih hb

section core
variable {m : ℕ} (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ)
  (cl : ℝ) (φ : ℕ → Fin m → ℝ)

/-- reached set -/
noncomputable def Rset (s k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => cl ^ k ≤ φ (s + k) i)

theorem step_edge (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (ν : ℕ) (l i : Fin m) (h : l = i ∨ Edges ν l i) : cl * φ ν l ≤ φ (ν + 1) i := by
  rw [hφs ν i]
  have h1 : C ν i l * φ ν l ≤ ∑ j, C ν i j * φ ν j :=
    Finset.single_le_sum (f := fun j => C ν i j * φ ν j)
      (fun j _ => mul_nonneg (hC ν i j) (hpos ν j)) (Finset.mem_univ l)
  have h2 : cl ≤ C ν i l := by
    rcases h with h | h
    · subst h; exact hdiag ν l
    · by_cases hil : i = l
      · subst hil; exact hdiag ν i
      · exact hedge ν i l hil h
  have := mul_le_mul_of_nonneg_right h2 (hpos ν l)
  linarith

theorem Rset_mono (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (s : ℕ) {l i : Fin m} {k : ℕ} (hl : l ∈ Rset cl φ s k)
    (h : l = i ∨ Edges (s + k) l i) : i ∈ Rset cl φ s (k + 1) := by
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  have := step_edge Edges C cl φ hC hpos hφs hdiag hedge (s + k) l i h
  rw [pow_succ, ← add_assoc]
  have h3 := mul_le_mul_of_nonneg_left hl hcl.le
  linarith

theorem Rset_mono' (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (s : ℕ) {i : Fin m} {k k' : ℕ} (hk : k ≤ k') (hi : i ∈ Rset cl φ s k) :
    i ∈ Rset cl φ s k' := by
  induction k', hk using Nat.le_induction with
  | base => exact hi
  | succ n _ ih => exact Rset_mono Edges C cl φ hC hpos hφs hdiag hedge hcl s ih (Or.inl rfl)

theorem Rset_grow (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (hB : AssumptionB' Edges B) (w0 n : ℕ) {j : Fin m}
    (hj : j ∈ Rset cl φ (w0 * B) (n * B)) (hne : Rset cl φ (w0 * B) (n * B) ≠ Finset.univ) :
    Rset cl φ (w0 * B) (n * B) ⊂ Rset cl φ (w0 * B) ((n + 1) * B) := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ Rset cl φ (w0 * B) (n * B) := by
    by_contra hcon; push Not at hcon
    exact hne (Finset.eq_univ_of_forall hcon)
  have hpath := hB.2 (w0 + n) j i
  obtain ⟨a, b, ha, hb, t, ht1, ht2, hab⟩ :=
    cross _ (fun z => z ∈ Rset cl φ (w0 * B) (n * B)) hpath hj hi
  have e1 : (w0 + n) * B = w0 * B + n * B := by ring
  have e2 : (w0 + n + 1) * B = w0 * B + n * B + B := by ring
  have e3 : (n + 1) * B = n * B + B := by ring
  rw [e1] at ht1; rw [e2] at ht2
  obtain ⟨k, hk⟩ : ∃ k, t = w0 * B + k := ⟨t - w0 * B, by omega⟩
  have hk1 : n * B ≤ k := by omega
  have hk2 : k + 1 ≤ (n + 1) * B := by rw [e3]; omega
  have ha' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) hk1 ha
  rw [hk] at hab
  have hb' := Rset_mono Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) ha' (Or.inr hab)
  have hb'' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) hk2 hb'
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨b, hb'', hb⟩
  · intro z hz
    exact Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
      (by rw [e3]; omega) hz

theorem Rset_count (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (hB : AssumptionB' Edges B) (w0 : ℕ) {j : Fin m}
    (hj : j ∈ Rset cl φ (w0 * B) 0) :
    ∀ n, Rset cl φ (w0 * B) (n * B) = Finset.univ ∨ n + 1 ≤ (Rset cl φ (w0 * B) (n * B)).card := by
  intro n
  induction n with
  | zero =>
    right; simp only [zero_mul, zero_add, Finset.one_le_card]; exact ⟨j, hj⟩
  | succ n ih =>
    by_cases hne : Rset cl φ (w0 * B) (n * B) = Finset.univ
    · left
      apply Finset.eq_univ_of_forall
      intro z
      have hz : z ∈ Rset cl φ (w0 * B) (n * B) := by rw [hne]; exact Finset.mem_univ z
      exact Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
        (Nat.mul_le_mul_right B (Nat.le_succ n)) hz
    · right
      rcases ih with h | h
      · exact absurd h hne
      · have hj' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
          (Nat.zero_le (n * B)) hj
        have := Finset.card_lt_card
          (Rset_grow Edges B C cl φ hC hpos hφs hdiag hedge hcl hB w0 n hj' hne)
        omega

end core

theorem phi_core {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl)
    (φ : ℕ → Fin m → ℝ) (hφ0 : ∀ i, φ 0 i = 1)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j) :
    ∀ ν i, phiLb m B cl ≤ φ ν i ∧ φ ν i ≤ phiUb m B cl := by
  have hC := C_nonneg hN
  obtain ⟨hB, hcl, hdiag, hoff, hcol⟩ := hN
  have hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j := fun ν i j h he => (hoff ν i j h).1 he
  have hm0 : 0 < m := by omega
  -- positivity and sum
  have hposs : ∀ ν i, 0 < φ ν i := by
    intro ν
    induction ν with
    | zero => intro i; rw [hφ0 i]; norm_num
    | succ n ih =>
      intro i
      rw [hφs n i]
      have hle : C n i i * φ n i ≤ ∑ j, C n i j * φ n j :=
        Finset.single_le_sum (f := fun j => C n i j * φ n j)
          (fun j _ => mul_nonneg (hC n i j) (ih j).le) (Finset.mem_univ i)
      have : 0 < C n i i * φ n i := mul_pos (lt_of_lt_of_le hcl (hdiag n i)) (ih i)
      linarith
  have hpos : ∀ ν i, 0 ≤ φ ν i := fun ν i => (hposs ν i).le
  have hsum : ∀ ν, ∑ i, φ ν i = m := by
    intro ν
    induction ν with
    | zero => simp [hφ0]
    | succ n ih =>
      simp_rw [hφs n]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol n, one_mul]
      exact ih
  have hcl1 : cl ≤ 1 := by
    have i0 : Fin m := ⟨0, hm0⟩
    have h1 : C 0 i0 i0 ≤ ∑ l, C 0 l i0 :=
      Finset.single_le_sum (f := fun l => C 0 l i0) (fun l _ => hC 0 l i0) (Finset.mem_univ i0)
    rw [hcol 0 i0] at h1
    linarith [hdiag 0 i0]
  have hdiagstep : ∀ t i, cl * φ t i ≤ φ (t + 1) i := fun t i =>
    step_edge Edges C cl φ hC hpos hφs hdiag hedge t i i (Or.inl rfl)
  have hiter : ∀ t k i, cl ^ k * φ t i ≤ φ (t + k) i := by
    intro t k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have := hdiagstep (t + k) i
      have h2 := mul_le_mul_of_nonneg_left (ih i) hcl.le
      rw [pow_succ, ← add_assoc]
      nlinarith
  set M := (m - 1) * B with hM
  have hlbeq : phiLb m B cl = cl ^ (2 * M) := by
    simp only [phiLb, hM]; ring_nf
  -- aligned windows: full reach
  have hfull : ∀ w0 i, cl ^ M ≤ φ (w0 * B + M) i := by
    intro w0 i
    obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, (1 : ℝ) ≤ φ (w0 * B) j := by
      have : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
      apply Finset.exists_le_of_sum_le Finset.univ_nonempty
      rw [hsum]; simp
    have hj0 : j ∈ Rset cl φ (w0 * B) 0 := by
      simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and, pow_zero, add_zero]
      exact hj
    have hc := Rset_count Edges B C cl φ hC hpos hφs hdiag hedge hcl hB w0 hj0 (m - 1)
    have huniv : Rset cl φ (w0 * B) ((m - 1) * B) = Finset.univ := by
      rcases hc with h | h
      · exact h
      · apply Finset.eq_univ_of_card
        have := Finset.card_le_univ (Rset cl φ (w0 * B) ((m - 1) * B))
        simp only [Fintype.card_fin] at this ⊢
        omega
    have hi : i ∈ Rset cl φ (w0 * B) ((m - 1) * B) := by rw [huniv]; exact Finset.mem_univ i
    simpa [Rset] using hi
  have hBM : B ≤ M := by
    rw [hM]; exact Nat.le_mul_of_pos_left B (by omega)
  have hlb : ∀ ν i, cl ^ (2 * M) ≤ φ ν i := by
    intro ν i
    by_cases hν : ν ≤ 2 * M
    · have h1 := hiter 0 ν i
      rw [hφ0 i, mul_one, zero_add] at h1
      exact (pow_le_pow_of_le_one hcl.le hcl1 hν).trans h1
    · push Not at hν
      have hBpos : 0 < B := hB.1
      obtain ⟨r, hr⟩ : ∃ r, r = ν - 2 * M := ⟨_, rfl⟩
      obtain ⟨w0, hw0⟩ : ∃ w0, w0 = (r + B - 1) / B := ⟨_, rfl⟩
      have hs1 : w0 * B ≤ r + B - 1 := by rw [hw0]; exact Nat.div_mul_le_self _ _
      have hs2 : r ≤ w0 * B := by
        have := Nat.lt_div_mul_add (a := r + B - 1) hBpos
        rw [← hw0] at this
        omega
      have hle : w0 * B + M ≤ ν := by omega
      obtain ⟨k, hk⟩ : ∃ k, ν = w0 * B + M + k := ⟨ν - (w0 * B + M), by omega⟩
      have h1 := hiter (w0 * B + M) k i
      rw [← hk] at h1
      have h2 := hfull w0 i
      have h3 : cl ^ k * cl ^ M ≤ cl ^ k * φ (w0 * B + M) i :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hcl.le k)
      have h4 : cl ^ (2 * M) ≤ cl ^ k * cl ^ M := by
        rw [← pow_add]
        exact pow_le_pow_of_le_one hcl.le hcl1 (by omega)
      linarith
  intro ν i
  refine ⟨hlbeq ▸ hlb ν i, ?_⟩
  -- upper bound
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin m, j0 ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  have hs := hsum ν
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
  have h1 : φ ν j0 ≤ ∑ j ∈ Finset.univ.erase i, φ ν j :=
    Finset.single_le_sum (f := fun j => φ ν j) (fun j _ => hpos ν j)
      (Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j0⟩)
  have h2 := hlb ν j0
  simp only [phiUb]
  have : (2 * (m - 1) * B) = 2 * M := by rw [hM]; ring
  rw [this]
  linarith

end SPushAux

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (hm : 2 ≤ m)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ, ∀ i : Fin m, phiLb m B cl ≤ φ ν i ∧ φ ν i ≤ phiUb m B cl :=
  SPushAux.phi_core hm Edges B C cl hN φ hrun.2.2.1 hrun.2.2.2.2.1
