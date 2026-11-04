-- Prove2me | solution 1 for SONATA.Push.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:35:11.815926+00:00
-- url     : https://prove2.me/submissions/5f0d3054-3334-4aa5-af0e-f507a022c984

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



namespace SPushChain

theorem conv_geom (ρ z : ℝ) (hρ0 : 0 ≤ ρ) (hρz : ρ < z) (ν : ℕ) :
    ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * z ^ t ≤ z ^ ν / (z - ρ) := by
  have hz : 0 < z := lt_of_le_of_lt hρ0 hρz
  have hne : z - ρ ≠ 0 := by linarith
  induction ν with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
    have : 0 < z - ρ := by linarith
    positivity
  | succ n ih =>
    have e : ∑ t ∈ Finset.range (n + 1), ρ ^ (n + 1 - 1 - t) * z ^ t =
        ρ * ∑ t ∈ Finset.range n, ρ ^ (n - 1 - t) * z ^ t + z ^ n := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        have ht' : t < n := Finset.mem_range.mp ht
        have : n + 1 - 1 - t = (n - 1 - t) + 1 := by omega
        rw [this, pow_succ]; ring
      · simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left ih hρ0
    have h2 : ρ * (z ^ n / (z - ρ)) + z ^ n = z ^ (n + 1) / (z - ρ) := by
      field_simp; ring
    linarith

/-- Small-gain chaining of (80), (81a), (81b), (84) via the transformation (49). -/
theorem chain (p X Y D : ℕ → ℝ) (hp0 : ∀ ν, 0 ≤ p ν) (hX0 : ∀ ν, 0 ≤ X ν) (hY0 : ∀ ν, 0 ≤ Y ν)
    (hD0 : ∀ ν, 0 ≤ D ν)
    (σ η a1 a2 A0 A1 A2 C1 C2 ρ z α gP gR : ℝ)
    (hσ0 : 0 ≤ σ) (hσz : σ < z) (hρ0 : 0 ≤ ρ) (hρz : ρ < z) (hρ1 : ρ ≤ 1)
    (hη : 0 ≤ η) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hgP0 : 0 ≤ gP) (hgR0 : 0 ≤ gR)
    (h80 : ∀ ν, p (ν + 1) ≤ σ * p ν + η * (a1 * X ν + a2 * Y ν))
    (h81a : ∀ ν, X ν ≤ A0 * ρ ^ (2 * ν) * X 0 +
      A1 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * (α ^ 2 * D t))
    (h81b : ∀ ν, Y ν ≤ A0 * ρ ^ (2 * ν) * Y 0 +
      A2 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * (8 * X t + 2 * α ^ 2 * D t))
    (h84 : ∀ ν, D ν ≤ C1 * p ν + C2 * Y ν)
    (hgP : η ≤ gP * (z - σ)) (hgR : 1 ≤ gR * (z - ρ))
    (hgain : (C1 * gP * a1 * (A1 * gR) + (C1 * gP * a2 + C2) * (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR))
      * α ^ 2 ≤ 1 / 2) :
    ∃ R, ∀ ν, p ν ≤ R * z ^ ν := by
  have hz : 0 < z := lt_of_le_of_lt hρ0 hρz
  have hzρ : 0 < z - ρ := by linarith
  have hzσ : 0 < z - σ := by linarith
  have hinv : 1 / (z - ρ) ≤ gR := by rw [div_le_iff₀ hzρ]; linarith
  have hρ2 : ∀ t : ℕ, ρ ^ (2 * t) ≤ z ^ t := by
    intro t
    rw [pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg ρ)
    nlinarith
  set X0' := A0 * X 0
  set Y0' := A0 * Y 0
  set c := C1 * p 0 + C1 * gP * a1 * X0' + (C1 * gP * a2 + C2) * (Y0' + 8 * A2 * gR * X0')
  set Γ := C1 * gP * a1 * (A1 * gR) + (C1 * gP * a2 + C2) * (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR)
  have hX0' : 0 ≤ X0' := mul_nonneg hA0 (hX0 0)
  have hY0' : 0 ≤ Y0' := mul_nonneg hA0 (hY0 0)
  have hc0 : 0 ≤ c := by
    have := hp0 0
    simp only [c]; positivity
  set R := p 0 + gP * a1 * (X0' + A1 * gR * (α ^ 2 * (2 * c))) +
    gP * a2 * (Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * (α ^ 2 * (2 * c)))
  refine ⟨R, fun ν => ?_⟩
  -- the transformation (49) up to K = ν
  set K := ν
  have hne : (Finset.range (K + 1)).Nonempty := Finset.nonempty_range_add_one
  let M : (ℕ → ℝ) → ℝ := fun s => (Finset.range (K + 1)).sup' hne (fun t => s t / z ^ t)
  have hM_le : ∀ s : ℕ → ℝ, ∀ t ≤ K, s t ≤ M s * z ^ t := by
    intro s t ht
    have h := Finset.le_sup' (fun t => s t / z ^ t) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    have hzt : 0 < z ^ t := pow_pos hz t
    calc s t = s t / z ^ t * z ^ t := by field_simp
      _ ≤ M s * z ^ t := mul_le_mul_of_nonneg_right h hzt.le
  have hM_bound : ∀ s : ℕ → ℝ, ∀ Bd : ℝ, (∀ t ≤ K, s t ≤ Bd * z ^ t) → M s ≤ Bd := by
    intro s Bd h
    apply Finset.sup'_le
    intro t ht
    have hzt : 0 < z ^ t := pow_pos hz t
    rw [div_le_iff₀ hzt]
    exact h t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have hM0 : ∀ s : ℕ → ℝ, (∀ t, 0 ≤ s t) → 0 ≤ M s := by
    intro s hs
    have := hM_le s 0 (Nat.zero_le _)
    have h0 := hs 0
    simp at this
    linarith
  set MX := M X
  set MY := M Y
  set MD := M D
  set MP := M p
  have hMX0 := hM0 X hX0
  have hMY0 := hM0 Y hY0
  have hMD0 := hM0 D hD0
  have hMP0 := hM0 p hp0
  set u := α ^ 2 * MD
  have hu0 : 0 ≤ u := mul_nonneg (sq_nonneg α) hMD0
  -- convolution bound
  have hconv : ∀ (s : ℕ → ℝ) (Ms : ℝ), 0 ≤ Ms → (∀ t ≤ K, 0 ≤ s t ∧ s t ≤ Ms * z ^ t) →
      ∀ t ≤ K, ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * s j ≤ Ms * gR * z ^ t := by
    intro s Ms hMs hs t ht
    calc ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * s j
        ≤ ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * (Ms * z ^ j) := by
          apply Finset.sum_le_sum; intro j hj
          have hj' : j ≤ K := by have := Finset.mem_range.mp hj; omega
          exact mul_le_mul_of_nonneg_left (hs j hj').2 (pow_nonneg hρ0 _)
      _ = Ms * ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * z ^ j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ Ms * (z ^ t / (z - ρ)) := mul_le_mul_of_nonneg_left (conv_geom ρ z hρ0 hρz t) hMs
      _ ≤ Ms * gR * z ^ t := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hMs
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right hinv (pow_nonneg hz.le t)
  -- (86)
  have hMX : MX ≤ X0' + A1 * gR * u := by
    apply hM_bound
    intro t ht
    have h1 := h81a t
    have h2 := hconv (fun j => α ^ 2 * D j) u hu0
      (fun j hj => ⟨mul_nonneg (sq_nonneg α) (hD0 j), by
        have := hM_le D j hj
        simp only [u, MD]; rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this (sq_nonneg α)⟩) t ht
    have h3 : A0 * ρ ^ (2 * t) * X 0 ≤ X0' * z ^ t := by
      simp only [X0']
      have := mul_le_mul_of_nonneg_left (hρ2 t) (mul_nonneg hA0 (hX0 0))
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h2 hA1
    beta_reduce at h4
    linarith
  -- (87)
  have hMY : MY ≤ Y0' + A2 * gR * (8 * MX + 2 * u) := by
    apply hM_bound
    intro t ht
    have h1 := h81b t
    have hW : 0 ≤ 8 * MX + 2 * u := by positivity
    have h2 := hconv (fun j => 8 * X j + 2 * α ^ 2 * D j) (8 * MX + 2 * u) hW
      (fun j hj => ⟨by have := hX0 j; have := hD0 j; positivity, by
        have hx := hM_le X j hj
        have hd := hM_le D j hj
        have hd' := mul_le_mul_of_nonneg_left hd (sq_nonneg α)
        simp only [u, MD, MX]
        nlinarith⟩) t ht
    have h3 : A0 * ρ ^ (2 * t) * Y 0 ≤ Y0' * z ^ t := by
      simp only [Y0']
      have := mul_le_mul_of_nonneg_left (hρ2 t) (mul_nonneg hA0 (hY0 0))
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h2 hA2
    beta_reduce at h4
    linarith
  -- (85)
  have hMP : MP ≤ p 0 + gP * (a1 * MX + a2 * MY) := by
    apply hM_bound
    have hQ : 0 ≤ a1 * MX + a2 * MY := by positivity
    have hW : 0 ≤ p 0 + gP * (a1 * MX + a2 * MY) := by have := hp0 0; positivity
    intro t ht
    induction t with
    | zero =>
      simp only [pow_zero, mul_one]
      have : 0 ≤ gP * (a1 * MX + a2 * MY) := by positivity
      linarith
    | succ n ih =>
      have ihn := ih (by omega)
      have hx := hM_le X n (by omega)
      have hy := hM_le Y n (by omega)
      have h1 := h80 n
      have hzn : 0 < z ^ n := pow_pos hz n
      have h2 : η * (a1 * X n + a2 * Y n) ≤ η * ((a1 * MX + a2 * MY) * z ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hη
        have := mul_le_mul_of_nonneg_left hx ha1
        have := mul_le_mul_of_nonneg_left hy ha2
        linarith
      have h3 : σ * p n ≤ σ * ((p 0 + gP * (a1 * MX + a2 * MY)) * z ^ n) :=
        mul_le_mul_of_nonneg_left ihn hσ0
      have h4 : η * (a1 * MX + a2 * MY) ≤ (z - σ) * (p 0 + gP * (a1 * MX + a2 * MY)) := by
        have := mul_le_mul_of_nonneg_right hgP hQ
        have := mul_nonneg hzσ.le (hp0 0)
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 hzn.le
      rw [pow_succ]
      linarith
  -- (88)
  have hMD : MD ≤ C1 * MP + C2 * MY := by
    apply hM_bound
    intro t ht
    have h1 := h84 t
    have := mul_le_mul_of_nonneg_left (hM_le p t ht) hC1
    have := mul_le_mul_of_nonneg_left (hM_le Y t ht) hC2
    linarith
  -- closing the loop
  have hY' : MY ≤ Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * u := by
    have := mul_le_mul_of_nonneg_left hMX (by positivity : (0:ℝ) ≤ 8 * A2 * gR)
    linarith
  have hloop : MD ≤ c + Γ * u := by
    have e1 := mul_le_mul_of_nonneg_left hMP hC1
    have e2 := mul_le_mul_of_nonneg_left hMX (by positivity : (0:ℝ) ≤ C1 * gP * a1)
    have e3 := mul_le_mul_of_nonneg_left hY' (by positivity : (0:ℝ) ≤ C1 * gP * a2 + C2)
    simp only [c, Γ]
    linarith
  have hΓu : Γ * u ≤ MD / 2 := by
    have : Γ * u = (Γ * α ^ 2) * MD := by simp only [u]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hgain hMD0
    linarith
  have hMDc : MD ≤ 2 * c := by linarith
  have hu2 : u ≤ α ^ 2 * (2 * c) := mul_le_mul_of_nonneg_left hMDc (sq_nonneg α)
  have hMX' : MX ≤ X0' + A1 * gR * (α ^ 2 * (2 * c)) := by
    have := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ A1 * gR)
    linarith
  have hY'' : MY ≤ Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * (α ^ 2 * (2 * c)) := by
    have := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ 8 * A2 * gR * (A1 * gR) + 2 * A2 * gR)
    linarith
  have hMPR : MP ≤ R := by
    have e1 := mul_le_mul_of_nonneg_left hMX' (by positivity : (0:ℝ) ≤ gP * a1)
    have e2 := mul_le_mul_of_nonneg_left hY'' (by positivity : (0:ℝ) ≤ gP * a2)
    simp only [R]
    linarith
  have := hM_le p ν le_rfl
  have hzν : 0 < z ^ ν := pow_pos hz ν
  linarith [mul_le_mul_of_nonneg_right hMPR hzν.le]

end SPushChain


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

/-- `Φ(s,k) = C^{s+k-1} ⋯ C^{s}` (product of `k` matrices starting at time `s`). -/
noncomputable def Phi {m : ℕ} (C : ℕ → Matrix (Fin m) (Fin m) ℝ) : ℕ → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, 0 => 1
  | s, k + 1 => C (s + k) * Phi C s k

section prod
variable {m : ℕ} (C : ℕ → Matrix (Fin m) (Fin m) ℝ)

theorem Phi_zero (s : ℕ) : Phi C s 0 = 1 := rfl
theorem Phi_succ (s k : ℕ) : Phi C s (k + 1) = C (s + k) * Phi C s k := rfl

theorem Phi_add (s a b : ℕ) : Phi C s (a + b) = Phi C (s + a) b * Phi C s a := by
  induction b with
  | zero => simp [Phi_zero]
  | succ n ih =>
    rw [← add_assoc, Phi_succ, ih, Phi_succ, Matrix.mul_assoc, add_assoc]

theorem Phi_nonneg (hC : ∀ ν i j, 0 ≤ C ν i j) (s k : ℕ) : ∀ i j, 0 ≤ Phi C s k i j := by
  induction k with
  | zero => intro i j; simp only [Phi_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j; rw [Phi_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hC _ _ _) (ih l j)

theorem Phi_colsum (hcol : ∀ ν j, ∑ i, C ν i j = 1) (s k : ℕ) : ∀ j, ∑ i, Phi C s k i j = 1 := by
  induction k with
  | zero => intro j; simp [Phi_zero, Matrix.one_apply]
  | succ n ih =>
    intro j
    simp only [Phi_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
    exact ih j

theorem Phi_le_one (hC : ∀ ν i j, 0 ≤ C ν i j) (hcol : ∀ ν j, ∑ i, C ν i j = 1) (s k : ℕ)
    (i j : Fin m) : Phi C s k i j ≤ 1 := by
  rw [← Phi_colsum C hcol s k j]
  exact Finset.single_le_sum (f := fun l => Phi C s k l j) (fun l _ => Phi_nonneg C hC s k l j)
    (Finset.mem_univ i)

theorem Phi_diag (hC : ∀ ν i j, 0 ≤ C ν i j) (cl : ℝ) (hcl : 0 ≤ cl) (hdiag : ∀ ν i, cl ≤ C ν i i)
    (s k : ℕ) : ∀ i, cl ^ k ≤ Phi C s k i i := by
  induction k with
  | zero => intro i; simp [Phi_zero]
  | succ n ih =>
    intro i
    rw [Phi_succ, Matrix.mul_apply]
    have h1 : C (s + n) i i * Phi C s n i i ≤ ∑ l, C (s + n) i l * Phi C s n l i :=
      Finset.single_le_sum (f := fun l => C (s + n) i l * Phi C s n l i)
        (fun l _ => mul_nonneg (hC _ _ _) (Phi_nonneg C hC s n l i)) (Finset.mem_univ i)
    have h2 := mul_le_mul (hdiag (s + n) i) (ih i) (pow_nonneg hcl n) ((hC _ _ _))
    rw [pow_succ']
    linarith

theorem mul_entry_ge_left (A M : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hM : ∀ i j, 0 ≤ M i j) (i j : Fin m) : A i i * M i j ≤ (A * M) i j := by
  rw [Matrix.mul_apply]
  exact Finset.single_le_sum (f := fun l => A i l * M l j) (fun l _ => mul_nonneg (hA i l) (hM l j))
    (Finset.mem_univ i)

theorem mul_entry_ge_right (A M : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hM : ∀ i j, 0 ≤ M i j) (i j : Fin m) : A i j * M j j ≤ (A * M) i j := by
  rw [Matrix.mul_apply]
  exact Finset.single_le_sum (f := fun l => A i l * M l j) (fun l _ => mul_nonneg (hA i l) (hM l j))
    (Finset.mem_univ j)

end prod

/-- Aligned blocks of `(m − 1)` windows have all entries `≥ c_ℓ^{(m−1)B}`. -/
theorem Phi_aligned_pos {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl) (w0 : ℕ)
    (i j : Fin m) : cl ^ ((m - 1) * B) ≤ Phi C (w0 * B) ((m - 1) * B) i j := by
  have hC := C_nonneg hN
  obtain ⟨hB, hcl, hdiag, hoff, hcol⟩ := hN
  obtain ⟨s, hs⟩ : ∃ s, s = w0 * B := ⟨_, rfl⟩
  rw [← hs]
  set C' : ℕ → Matrix (Fin m) (Fin m) ℝ := fun t => C (s + t)
  set E' : ℕ → Fin m → Fin m → Prop := fun t => Edges (s + t)
  set φ' : ℕ → Fin m → ℝ := fun t l => Phi C s t l j
  have hC' : ∀ ν i j, 0 ≤ C' ν i j := fun ν i j => hC _ i j
  have hpos' : ∀ ν i, 0 ≤ φ' ν i := fun ν l => Phi_nonneg C hC s ν l j
  have hφs' : ∀ ν i, φ' (ν + 1) i = ∑ l, C' ν i l * φ' ν l := by
    intro ν l; simp only [φ', C', Phi_succ, Matrix.mul_apply]
  have hdiag' : ∀ ν i, cl ≤ C' ν i i := fun ν i => hdiag _ i
  have hedge' : ∀ ν i j, i ≠ j → E' ν j i → cl ≤ C' ν i j :=
    fun ν i j h he => (hoff (s + ν) i j h).1 he
  have hB' : AssumptionB' E' B := by
    refine ⟨hB.1, fun n a c => ?_⟩
    have hp := hB.2 (w0 + n) a c
    refine Relation.ReflTransGen.mono ?_ _ _ hp
    rintro u v ⟨t, ht1, ht2, he⟩
    have h1 : (w0 + n) * B = s + n * B := by rw [hs]; ring
    have h2 : (w0 + n + 1) * B = s + n * B + B := by rw [hs]; ring
    have h3 : (n + 1) * B = n * B + B := by ring
    rw [h1] at ht1; rw [h2] at ht2
    refine ⟨t - s, ?_, ?_, ?_⟩
    · generalize n * B = N at *; omega
    · rw [h3]; generalize n * B = N at *; omega
    · have : s + (t - s) = t := by generalize n * B = N at *; omega
      simp only [E']; rw [this]; exact he
  have hj0 : j ∈ Rset cl φ' (0 * B) 0 := by
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and, pow_zero, add_zero, zero_mul]
    simp [φ', Phi_zero]
  have hc := Rset_count E' B C' cl φ' hC' hpos' hφs' hdiag' hedge' hcl hB' 0 hj0 (m - 1)
  have huniv : Rset cl φ' (0 * B) ((m - 1) * B) = Finset.univ := by
    rcases hc with h | h
    · exact h
    · apply Finset.eq_univ_of_card
      have := Finset.card_le_univ (Rset cl φ' (0 * B) ((m - 1) * B))
      simp only [Fintype.card_fin] at this ⊢
      omega
  have hi : i ∈ Rset cl φ' (0 * B) ((m - 1) * B) := by rw [huniv]; exact Finset.mem_univ i
  simpa [Rset, φ'] using hi

/-- Every block of length `2(m − 1)B` has all entries `≥ c_ℓ^{2(m−1)B}`. -/
theorem Phi_block_pos {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl) (s : ℕ)
    (i j : Fin m) : cl ^ (2 * ((m - 1) * B)) ≤ Phi C s (2 * ((m - 1) * B)) i j := by
  have hC := C_nonneg hN
  have hcl := hN.2.1
  have hdiag := hN.2.2.1
  have hB0 : 0 < B := hN.1.1
  set M := (m - 1) * B
  have hBM : B ≤ M := Nat.le_mul_of_pos_left B (by omega)
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = (s + B - 1) / B := ⟨_, rfl⟩
  have hs1 : w0 * B ≤ s + B - 1 := by rw [hw0]; exact Nat.div_mul_le_self _ _
  have hs2 : s ≤ w0 * B := by
    have := Nat.lt_div_mul_add (a := s + B - 1) hB0
    rw [← hw0] at this; omega
  obtain ⟨r1, hr1⟩ : ∃ r1, w0 * B = s + r1 := ⟨w0 * B - s, by omega⟩
  obtain ⟨r2, hr2⟩ : ∃ r2, 2 * M = r1 + (M + r2) := ⟨2 * M - r1 - M, by omega⟩
  rw [hr2, Phi_add C s r1 (M + r2), ← hr1]
  have hP1 := Phi_nonneg C hC
  have e1 := mul_entry_ge_right (Phi C (w0 * B) (M + r2)) (Phi C s r1) (hP1 _ _) (hP1 _ _) i j
  rw [Phi_add C (w0 * B) M r2] at e1 ⊢
  have e2 := mul_entry_ge_left (Phi C (w0 * B + M) r2) (Phi C (w0 * B) M) (hP1 _ _) (hP1 _ _) i j
  have d1 := Phi_diag C hC cl hcl.le hdiag (w0 * B + M) r2 i
  have d2 := Phi_diag C hC cl hcl.le hdiag s r1 j
  have a1 := Phi_aligned_pos hm Edges B C cl hN w0 i j
  have h3 : cl ^ r2 * cl ^ M ≤ Phi C (w0 * B + M) r2 i i * Phi C (w0 * B) M i j :=
    mul_le_mul d1 a1 (pow_nonneg hcl.le _) (hP1 _ _ _ _)
  have h4 : cl ^ r2 * cl ^ M * cl ^ r1 ≤
      (Phi C (w0 * B + M) r2 * Phi C (w0 * B) M) i j * Phi C s r1 j j :=
    mul_le_mul (h3.trans e2) d2 (pow_nonneg hcl.le _)
      ((mul_nonneg (pow_nonneg hcl.le _) (pow_nonneg hcl.le _)).trans (h3.trans e2))
  have e : cl ^ (r1 + (M + r2)) = cl ^ r2 * cl ^ M * cl ^ r1 := by ring
  rw [e]
  exact h4.trans e1

/-- One contraction step for rows averaged by a column-stochastic matrix with entries `≥ η`. -/
theorem row_contract {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (Q : Matrix (Fin m) (Fin m) ℝ) (η S : ℝ)
    (hQ : ∀ l j, η ≤ Q l j) (hcol : ∀ j, ∑ l, Q l j = 1) (ha : ∀ l l', a l - a l' ≤ S)
    (j k : Fin m) : ∑ l, a l * Q l j - ∑ l, a l * Q l k ≤ (1 - m * η) * S := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨l0, -, hl0⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have e : ∑ l, a l * Q l j - ∑ l, a l * Q l k = ∑ l, (a l - a l0) * (Q l j - Q l k) := by
    have h1 : ∑ l, a l0 * Q l j = a l0 := by rw [← Finset.mul_sum, hcol, mul_one]
    have h2 : ∑ l, a l0 * Q l k = a l0 := by rw [← Finset.mul_sum, hcol, mul_one]
    have : ∑ l, (a l - a l0) * (Q l j - Q l k) =
        ∑ l, a l * Q l j - ∑ l, a l * Q l k - (∑ l, a l0 * Q l j - ∑ l, a l0 * Q l k) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [this, h1, h2]; ring
  rw [e]
  have hb : ∀ l, (a l - a l0) * (Q l j - Q l k) ≤ S * (Q l j - η) := by
    intro l
    have h0 : 0 ≤ a l - a l0 := sub_nonneg.mpr (hl0 l (Finset.mem_univ l))
    have h1 : (a l - a l0) * (Q l j - Q l k) ≤ (a l - a l0) * (Q l j - η) :=
      mul_le_mul_of_nonneg_left (by linarith [hQ l k]) h0
    have h2 : (a l - a l0) * (Q l j - η) ≤ S * (Q l j - η) :=
      mul_le_mul_of_nonneg_right (ha l l0) (by linarith [hQ l j])
    linarith
  refine (Finset.sum_le_sum fun l _ => hb l).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcol]
  simp; ring

/-- Geometric decay of the column spread of `Φ(s,k)`. -/
theorem Phi_spread {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl) :
    ∀ n s r : ℕ, ∀ i j k : Fin m,
      Phi C s (n * (2 * ((m - 1) * B)) + r) i j - Phi C s (n * (2 * ((m - 1) * B)) + r) i k ≤
        (1 - m * cl ^ (2 * ((m - 1) * B))) ^ n := by
  have hC := C_nonneg hN
  have hcol := hN.2.2.2.2
  set L := 2 * ((m - 1) * B)
  intro n
  induction n with
  | zero =>
    intro s r i j k
    simp only [zero_mul, zero_add, pow_zero]
    have := Phi_le_one C hC hcol s r i j
    have := Phi_nonneg C hC s r i k
    linarith
  | succ n ih =>
    intro s r i j k
    have e : (n + 1) * L + r = L + (n * L + r) := by ring
    rw [e, Phi_add, Matrix.mul_apply, Matrix.mul_apply]
    have := row_contract (by omega) (fun l => Phi C (s + L) (n * L + r) i l) (Phi C s L)
      (cl ^ L) ((1 - m * cl ^ L) ^ n) (fun l j => Phi_block_pos hm Edges B C cl hN s l j)
      (Phi_colsum C hcol s L) (fun l l' => ih (s + L) r i l l') j k
    rw [pow_succ]
    linarith

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

section rep
variable {m d : ℕ} (C : ℕ → Matrix (Fin m) (Fin m) ℝ)

theorem phi_rep (φ : ℕ → Fin m → ℝ) (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (s k : ℕ) : ∀ i, φ (s + k) i = ∑ j, Phi C s k i j * φ s j := by
  induction k with
  | zero => intro i; simp [Phi_zero, Matrix.one_apply]
  | succ n ih =>
    intro i
    rw [← add_assoc, hφs, Phi_succ]
    simp_rw [Matrix.mul_apply, ih, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro l _; ring

theorem mix_mul (A M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → E d) (i : Fin m) :
    ∑ l, A i l • ∑ j, M l j • v j = ∑ j, (A * M) i j • v j := by
  simp_rw [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem u_rep (u e : ℕ → Fin m → E d)
    (hu : ∀ ν i, u (ν + 1) i = ∑ j, C ν i j • (u ν j + e ν j)) :
    ∀ ν i, u ν i = ∑ j, Phi C 0 ν i j • u 0 j +
      ∑ t ∈ Finset.range ν, ∑ j, Phi C t (ν - t) i j • e t j := by
  intro ν
  induction ν with
  | zero => intro i; simp [Phi_zero, Matrix.one_apply]
  | succ n ih =>
    intro i
    have e1 : C n * Phi C 0 n = Phi C 0 (n + 1) := by rw [Phi_succ, zero_add]
    have hA : ∑ l, C n i l • ∑ j, Phi C 0 n l j • u 0 j = ∑ j, Phi C 0 (n + 1) i j • u 0 j := by
      rw [mix_mul, e1]
    have hB : ∀ t ∈ Finset.range n, ∑ l, C n i l • ∑ j, Phi C t (n - t) l j • e t j =
        ∑ j, Phi C t (n + 1 - t) i j • e t j := by
      intro t ht
      have ht' : t < n := Finset.mem_range.mp ht
      have e2 : C n * Phi C t (n - t) = Phi C t (n + 1 - t) := by
        have h1 : n + 1 - t = (n - t) + 1 := by omega
        have h2 : t + (n - t) = n := by omega
        rw [h1, Phi_succ, h2]
      rw [mix_mul, e2]
    have hE : ∑ l, C n i l • e n l = ∑ j, Phi C n (n + 1 - n) i j • e n j := by
      have e3 : Phi C n (n + 1 - n) = C n := by
        rw [show n + 1 - n = 0 + 1 by omega, Phi_succ, Phi_zero, add_zero, Matrix.mul_one]
      rw [e3]
    have hsplit : ∑ j, C n i j • (u n j + e n j) =
        ∑ l, C n i l • ∑ j, Phi C 0 n l j • u 0 j +
          ∑ t ∈ Finset.range n, ∑ l, C n i l • ∑ j, Phi C t (n - t) l j • e t j +
            ∑ l, C n i l • e n l := by
      simp_rw [smul_add, Finset.sum_add_distrib]
      congr 1
      simp_rw [ih, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
      congr 1
      rw [Finset.sum_comm]
    rw [hu n i, hsplit, hA, Finset.sum_congr rfl hB, hE, Finset.sum_range_succ, add_assoc]

end rep

end SPushAux

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem norm_coef_sum {m d : ℕ} (κ : Fin m → ℝ) (w : Fin m → E d) (K : ℝ)
    (hκ : ∀ j, |κ j| ≤ K) : ‖∑ j, κ j • w j‖ ≤ K * ∑ j, ‖w j‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hκ j) (norm_nonneg _)

/-- The perturbed push-sum bound (82)–(83), generic form. -/
theorem ps_bound {m d : ℕ} (hm : 0 < m) (C : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hC : ∀ ν i j, 0 ≤ C ν i j) (hcol : ∀ ν j, ∑ i, C ν i j = 1)
    (φ : ℕ → Fin m → ℝ) (hφ0 : ∀ i, φ 0 i = 1) (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (u e : ℕ → Fin m → E d) (hu : ∀ ν i, u (ν + 1) i = ∑ j, C ν i j • (u ν j + e ν j))
    (lb Cc lam : ℝ) (hlb0 : 0 < lb) (hlb : ∀ ν i, lb ≤ φ ν i)
    (hspread : ∀ s k i j l, Phi C s k i j - Phi C s k i l ≤ Cc * lam ^ k) (ν : ℕ) (i : Fin m) :
    ‖(φ ν i)⁻¹ • u ν i - (1 / (m : ℝ)) • ∑ j, u ν j‖ ≤
      Cc / lb * (lam ^ ν * ∑ j, ‖u 0 j - (1 / (m : ℝ)) • ∑ l, u 0 l‖ +
        ∑ t ∈ Finset.range ν, lam ^ (ν - t) * ∑ j, ‖e t j‖) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsumφ : ∀ t, ∑ l, φ t l = m := by
    intro t
    induction t with
    | zero => simp [hφ0]
    | succ n ih =>
      simp_rw [hφs n]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hcol n, one_mul]; exact ih
  have hsumu : ∀ ν, ∑ i, u ν i = ∑ j, u 0 j + ∑ t ∈ Finset.range ν, ∑ j, e t j := by
    intro ν
    induction ν with
    | zero => simp
    | succ n ih =>
      simp_rw [hu n]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hcol n, one_smul, Finset.sum_add_distrib]
      rw [ih, Finset.sum_range_succ]; abel
  -- coefficient bound
  have hcoef : ∀ t k j, |Phi C t k i j / φ (t + k) i - 1 / m| ≤ Cc * lam ^ k / lb := by
    intro t k j
    have hq := phi_rep C φ hφs t k i
    have hqpos : 0 < φ (t + k) i := lt_of_lt_of_le hlb0 (hlb _ _)
    have e : Phi C t k i j / φ (t + k) i - 1 / m =
        ((1 / (m : ℝ)) * ∑ l, φ t l * (Phi C t k i j - Phi C t k i l)) / φ (t + k) i := by
      rw [hq]
      have : ∑ l, φ t l * (Phi C t k i j - Phi C t k i l) =
          m * Phi C t k i j - ∑ l, Phi C t k i l * φ t l := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumφ t]
        congr 1; apply Finset.sum_congr rfl; intro l _; ring
      rw [this, ← hq]
      field_simp
    rw [e, abs_div, abs_of_pos hqpos]
    have hnum : |(1 / (m : ℝ)) * ∑ l, φ t l * (Phi C t k i j - Phi C t k i l)| ≤ Cc * lam ^ k := by
      rw [abs_mul, abs_of_pos (by positivity)]
      have h1 : |∑ l, φ t l * (Phi C t k i j - Phi C t k i l)| ≤ ∑ l, φ t l * (Cc * lam ^ k) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [abs_mul, abs_of_pos (lt_of_lt_of_le hlb0 (hlb _ _))]
        apply mul_le_mul_of_nonneg_left _ (lt_of_lt_of_le hlb0 (hlb _ _)).le
        rw [abs_le]; constructor
        · have := hspread t k i l j; linarith
        · exact hspread t k i j l
      rw [← Finset.sum_mul, hsumφ t] at h1
      calc 1 / (m : ℝ) * |∑ l, φ t l * (Phi C t k i j - Phi C t k i l)|
          ≤ 1 / (m : ℝ) * (m * (Cc * lam ^ k)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Cc * lam ^ k := by field_simp
    have hCc : 0 ≤ Cc * lam ^ k := (abs_nonneg _).trans hnum
    calc |(1 / (m : ℝ)) * ∑ l, φ t l * (Phi C t k i j - Phi C t k i l)| / φ (t + k) i
        ≤ Cc * lam ^ k / φ (t + k) i := div_le_div_of_nonneg_right hnum hqpos.le
      _ ≤ Cc * lam ^ k / lb := div_le_div_of_nonneg_left hCc hlb0 (hlb _ _)
  -- decomposition
  set ub0 := (1 / (m : ℝ)) • ∑ l, u 0 l
  have hκ0 : ∑ j, (Phi C 0 ν i j / φ ν i - 1 / m) = 0 := by
    have hq := phi_rep C φ hφs 0 ν i
    simp only [zero_add, hφ0, mul_one] at hq
    have hqpos : 0 < φ ν i := lt_of_lt_of_le hlb0 (hlb _ _)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hq, div_self hqpos.ne', Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) * (1 / m) = 1 := by field_simp
    linarith
  have hdec : (φ ν i)⁻¹ • u ν i - (1 / (m : ℝ)) • ∑ j, u ν j =
      ∑ j, (Phi C 0 ν i j / φ ν i - 1 / m) • (u 0 j - ub0) +
        ∑ t ∈ Finset.range ν, ∑ j, (Phi C t (ν - t) i j / φ ν i - 1 / m) • e t j := by
    have h0 : ∑ j, (Phi C 0 ν i j / φ ν i - 1 / m) • ub0 = 0 := by
      rw [← Finset.sum_smul, hκ0, zero_smul]
    have h1 : ∑ j, (Phi C 0 ν i j / φ ν i - 1 / m) • (u 0 j - ub0) =
        ∑ j, (Phi C 0 ν i j / φ ν i - 1 / m) • u 0 j := by
      simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, h0, sub_zero]
    have hel : ∀ (κ : Fin m → ℝ) (w : Fin m → E d),
        ∑ j, (κ j / φ ν i - 1 / (m : ℝ)) • w j =
          (φ ν i)⁻¹ • ∑ j, κ j • w j - (1 / (m : ℝ)) • ∑ j, w j := by
      intro κ w
      simp_rw [sub_smul, Finset.sum_sub_distrib, div_eq_inv_mul, mul_smul, Finset.smul_sum]
    rw [h1, hel]
    simp_rw [hel]
    rw [u_rep C u e hu ν i, hsumu ν, smul_add, smul_add, Finset.smul_sum, Finset.smul_sum,
      Finset.sum_sub_distrib]
    simp only [Finset.smul_sum]
    abel
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  have hA := norm_coef_sum (fun j => Phi C 0 ν i j / φ ν i - 1 / m) (fun j => u 0 j - ub0)
    (Cc * lam ^ ν / lb) (fun j => by simpa using hcoef 0 ν j)
  have hB : ‖∑ t ∈ Finset.range ν, ∑ j, (Phi C t (ν - t) i j / φ ν i - 1 / m) • e t j‖ ≤
      ∑ t ∈ Finset.range ν, Cc * lam ^ (ν - t) / lb * ∑ j, ‖e t j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have ht' : t ≤ ν := (Finset.mem_range.mp ht).le
    apply norm_coef_sum
    intro j
    have := hcoef t (ν - t) j
    rwa [Nat.add_sub_cancel' ht'] at this
  have e : Cc / lb * (lam ^ ν * ∑ j, ‖u 0 j - ub0‖ +
      ∑ t ∈ Finset.range ν, lam ^ (ν - t) * ∑ j, ‖e t j‖) =
      Cc * lam ^ ν / lb * ∑ j, ‖u 0 j - ub0‖ +
        ∑ t ∈ Finset.range ν, Cc * lam ^ (ν - t) / lb * ∑ j, ‖e t j‖ := by
    rw [mul_add]; congr 1
    · ring
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
  rw [e]
  exact add_le_add hA hB

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

/-- Squared-sum form of the push-sum bound. -/
theorem sq_bound {m d : ℕ} (w : Fin m → E d) (K lam A : ℝ) (ν : ℕ) (Eb : ℕ → ℝ)
    (hK : 0 ≤ K) (hl0 : 0 < lam) (hl1 : lam < 1) (hA : 0 ≤ A) (hE : ∀ t, 0 ≤ Eb t)
    (hw : ∀ i, ‖w i‖ ≤ K * (lam ^ ν * A + ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t)) :
    sqn w ≤ 2 * m * K ^ 2 * (lam ^ (2 * ν) * A ^ 2 +
      lam / (1 - lam) * ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t ^ 2) := by
  set a := lam ^ ν * A
  set b := ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hl0.le _) (hE t)
  have h1 : sqn w ≤ m * (K * (a + b)) ^ 2 := by
    unfold sqn
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, (K * (a + b)) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
      _ = m * (K * (a + b)) ^ 2 := by simp
  have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hgeo : ∑ t ∈ Finset.range ν, lam ^ (ν - t) ≤ lam / (1 - lam) := by
    have := SPushChain.conv_geom lam 1 hl0.le hl1 ν
    simp only [one_pow, mul_one] at this
    have e : ∑ t ∈ Finset.range ν, lam ^ (ν - t) = lam * ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht
      have : ν - t = (ν - 1 - t) + 1 := by have := Finset.mem_range.mp ht; omega
      rw [this, pow_succ]; ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left this hl0.le
    rw [mul_one_div] at h
    exact h
  have hb2 : b ^ 2 ≤ lam / (1 - lam) * ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range ν)
      (r := fun t => lam ^ (ν - t) * Eb t) (f := fun t => lam ^ (ν - t))
      (g := fun t => lam ^ (ν - t) * Eb t ^ 2)
      (fun t _ => pow_nonneg hl0.le _) (fun t _ => mul_nonneg (pow_nonneg hl0.le _) (sq_nonneg _))
      (fun t _ => le_of_eq (by ring))
    have hg0 : 0 ≤ ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t ^ 2 :=
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hl0.le _) (sq_nonneg _)
    exact hcs.trans (mul_le_mul_of_nonneg_right hgeo hg0)
  have ha2 : a ^ 2 = lam ^ (2 * ν) * A ^ 2 := by simp only [a]; rw [mul_pow, ← pow_mul, mul_comm ν 2]
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc sqn w ≤ m * (K * (a + b)) ^ 2 := h1
    _ = m * K ^ 2 * (a + b) ^ 2 := by ring
    _ ≤ m * K ^ 2 * (2 * (a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ m * K ^ 2 * (2 * (a ^ 2 + lam / (1 - lam) *
          ∑ t ∈ Finset.range ν, lam ^ (ν - t) * Eb t ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = _ := by rw [ha2]; ring

theorem sum_norm_sq_le {m d : ℕ} (v : Fin m → E d) : (∑ j, ‖v j‖) ^ 2 ≤ m * sqn v := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖v j‖)
  simpa [sqn] using this

/-- The step `x^{t+1} − x^t` is controlled by the consensus error and the direction. -/
theorem dx_bound {m d : ℕ} {K : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl) (hα0 : 0 < α)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) (t : ℕ) :
    sqn (fun i => x (t + 1) i - x t i) ≤
      (m : ℝ) ^ 2 * (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)) := by
  have hpos := phi_pos hN hrun
  have hC := C_nonneg hN
  obtain ⟨_, _, _, _, hφs, hxs, _⟩ := hrun
  set xb := wavg (φ t) (x t)
  set p := wperp (φ t) (x t)
  set dd := dir x xh t
  set s := ∑ j, ‖p j‖
  set q := α * ∑ j, ‖dd j‖
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hq0 : 0 ≤ q := mul_nonneg hα0.le (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hi : ∀ i, ‖x (t + 1) i - x t i‖ ≤ 2 * s + q := by
    intro i
    set w : Fin m → ℝ := fun j => (φ (t + 1) i)⁻¹ * (C t i j * φ t j)
    have hw0 : ∀ j, 0 ≤ w j := fun j =>
      mul_nonneg (inv_nonneg.mpr (hpos _ _).le) (mul_nonneg (hC _ _ _) (hpos _ _).le)
    have hw1 : ∑ j, w j = 1 := by
      simp only [w]; rw [← Finset.mul_sum, ← hφs t i]; exact inv_mul_cancel₀ (hpos _ _).ne'
    have hwle : ∀ j, w j ≤ 1 := fun j => by
      rw [← hw1]; exact Finset.single_le_sum (f := w) (fun l _ => hw0 l) (Finset.mem_univ j)
    have hx' : x (t + 1) i = ∑ j, w j • xhalf α x xh t j := by
      rw [hxs t i, Finset.smul_sum]; simp_rw [smul_smul]; rfl
    have hxj : ∀ j, xhalf α x xh t j = xb + (p j + α • dd j) := by
      intro j; simp only [xhalf, p, dd, wperp]; abel
    have hdiff : x (t + 1) i - x t i = ∑ j, w j • (p j + α • dd j) - p i := by
      rw [hx']
      simp_rw [hxj, smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul]
      simp only [p, wperp]; abel
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖∑ j, w j • (p j + α • dd j)‖ ≤ ∑ j, (‖p j‖ + α * ‖dd j‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 j)]
      have h2 : ‖p j + α • dd j‖ ≤ ‖p j‖ + α * ‖dd j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα0]
      have h3 : 0 ≤ ‖p j‖ + α * ‖dd j‖ := by positivity
      calc w j * ‖p j + α • dd j‖ ≤ 1 * (‖p j‖ + α * ‖dd j‖) :=
            mul_le_mul (hwle j) h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h4 : ∑ j, (‖p j‖ + α * ‖dd j‖) = s + q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h5 : ‖p i‖ ≤ s := Finset.single_le_sum (f := fun j => ‖p j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  have hs2 : s ^ 2 ≤ m * sqn p := sum_norm_sq_le p
  have hq2 : q ^ 2 ≤ m * (α ^ 2 * sqn dd) := by
    have := sum_norm_sq_le dd
    simp only [q]; rw [mul_pow]
    nlinarith [sq_nonneg α]
  unfold sqn
  calc ∑ i, ‖x (t + 1) i - x t i‖ ^ 2 ≤ ∑ _i : Fin m, (2 * s + q) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
    _ = m * (2 * s + q) ^ 2 := by simp
    _ ≤ m * (8 * s ^ 2 + 2 * q ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
        nlinarith [sq_nonneg (2 * s - q)]
    _ ≤ m * (8 * (m * sqn p) + 2 * (m * (α ^ 2 * sqn dd))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m); linarith
    _ = (m : ℝ) ^ 2 * (8 * sqn p + 2 * α ^ 2 * sqn dd) := by ring

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem shift_sum (lam : ℝ) (ν : ℕ) (F : ℕ → ℝ) :
    ∑ t ∈ Finset.range ν, lam ^ (ν - t) * F t = lam * ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * F t := by
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht
  have : ν - t = (ν - 1 - t) + 1 := by have := Finset.mem_range.mp ht; omega
  rw [this, pow_succ]; ring

/-- Network constants: spread bound `Φ(s,k)ᵢⱼ − Φ(s,k)ᵢₗ ≤ C λ^k` with `λ ∈ (0,1)`. -/
theorem spread_geom {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl) :
    ∃ lam Cc : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < Cc ∧
      ∀ s k i j l, Phi C s k i j - Phi C s k i l ≤ Cc * lam ^ k := by
  have hC := C_nonneg hN
  have hcol := hN.2.2.2.2
  have hcl := hN.2.1
  have hB0 : 0 < B := hN.1.1
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * ((m - 1) * B) := ⟨_, rfl⟩
  have hL1 : 2 ≤ L := by
    rw [hL]
    have : 1 ≤ (m - 1) * B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set η := cl ^ L with hη
  have hη0 : 0 < η := pow_pos hcl L
  have hmη : (m : ℝ) * η ≤ 1 := by
    have i0 : Fin m := ⟨0, by omega⟩
    have h := Phi_colsum C hcol 0 L i0
    have : ∑ _l : Fin m, η ≤ ∑ l, Phi C 0 L l i0 := Finset.sum_le_sum fun l _ => by
      rw [hη, hL]; exact Phi_block_pos hm Edges B C cl hN 0 l i0
    simp at this; linarith
  set lam := 1 - m * η / L
  have hfrac : (m : ℝ) * η / L ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hlam0 : 0 < lam := by simp only [lam]; linarith
  have hlam1 : lam < 1 := by simp only [lam]; have : 0 < (m : ℝ) * η / L := by positivity
                             linarith
  have hθ0 : 0 ≤ 1 - (m : ℝ) * η := by linarith
  have hθ : 1 - (m : ℝ) * η ≤ lam ^ L := by
    have := one_add_mul_le_pow (a := -((m : ℝ) * η / L)) (by linarith) L
    have e : (1 : ℝ) + L * -((m : ℝ) * η / L) = 1 - m * η := by field_simp; ring
    rw [e] at this
    simpa [lam, sub_eq_add_neg] using this
  refine ⟨lam, 1 / lam ^ L, hlam0, hlam1, by positivity, ?_⟩
  intro s k i j l
  have hk : k = k / L * L + k % L := (Nat.div_add_mod' k L).symm
  have hsp := Phi_spread hm Edges B C cl hN (k / L) s (k % L) i j l
  rw [← hL, ← hk, ← hη] at hsp
  have h1 : (1 - (m : ℝ) * η) ^ (k / L) ≤ lam ^ (L * (k / L)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ hθ0 hθ _
  have hr : k % L ≤ L := (Nat.mod_lt k (by omega)).le
  have h2 : lam ^ L ≤ lam ^ (k % L) := pow_le_pow_of_le_one hlam0.le hlam1.le hr
  have h3 : lam ^ (L * (k / L)) * lam ^ L ≤ lam ^ k := by
    calc lam ^ (L * (k / L)) * lam ^ L ≤ lam ^ (L * (k / L)) * lam ^ (k % L) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hlam0.le _)
      _ = lam ^ k := by rw [← pow_add]; congr 1; rw [mul_comm]; exact hk.symm
  have hLp : 0 < lam ^ L := pow_pos hlam0 L
  have h4 : lam ^ (L * (k / L)) ≤ 1 / lam ^ L * lam ^ k := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hLp]; exact h3
  linarith

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem L42_main {m d : ℕ} (hm : 2 ≤ m) (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ)
    (μ L : ℝ) (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li) :
    ∃ c0 ρB : ℝ, 0 < c0 ∧ 0 < ρB ∧ ρB < 1 ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ x y xh : ℕ → Fin m → E d, ∀ φ : ℕ → Fin m → ℝ, IsRun K f G ft C α x y xh φ →
      ∀ ν : ℕ,
        sqn (wperp (φ ν) (x ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (x 0))
              + 2 * c0 ^ 2 * ρB ^ 2 / (1 - ρB) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) ∧
        sqn (wperp (φ ν) (y ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (y 0))
              + 2 * c0 ^ 2 * ρB ^ 2 * m * Lmx Li ^ 2 / (phiLb m B cl ^ 2 * (1 - ρB)) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) *
                    (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)) := by
  have hm0 : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hC := C_nonneg hN
  have hcol := hN.2.2.2.2
  have hcl := hN.2.1
  obtain ⟨lam, Cc, hl0, hl1, hCc, hsp⟩ := spread_geom hm Edges B C cl hN
  obtain ⟨lb, hlb_def⟩ : ∃ v, v = phiLb m B cl := ⟨_, rfl⟩
  have hlb0 : 0 < lb := by rw [hlb_def, phiLb]; exact pow_pos hcl _
  have hcl1 : cl ≤ 1 := by
    have i0 : Fin m := ⟨0, hm0⟩
    have h := Finset.single_le_sum (f := fun l => C 0 l i0) (fun l _ => hC 0 l i0)
      (Finset.mem_univ i0)
    rw [hcol 0 i0] at h; linarith [hN.2.2.1 0 i0]
  have hlb1 : lb ≤ 1 := by rw [hlb_def, phiLb]; exact pow_le_one₀ hcl.le hcl1
  obtain ⟨Kc, hK_def⟩ : ∃ v, v = Cc / lb := ⟨_, rfl⟩
  have hK0 : 0 < Kc := by rw [hK_def]; positivity
  have hLm : 0 ≤ Lmx Li := (h1 ⟨0, hm0⟩).2.1.le.trans (le_ciSup (Set.finite_range Li).bddAbove _)
  refine ⟨(m : ℝ) ^ 2 * Kc, lam, by positivity, hl0, hl1, ?_⟩
  intro α hα0 hα1 x y xh φ hrun ν
  have hA := hP.2.1
  have hxK := x_mem hA hN hα0 hα1 hrun
  have hpos := phi_pos hN hrun
  have hsum := phi_sum hN hrun
  have hφm : ∀ t j, φ t j ≤ m := fun t j => by
    rw [← hsum t]
    exact Finset.single_le_sum (f := fun l => φ t l) (fun l _ => (hpos t l).le) (Finset.mem_univ j)
  have hlb : ∀ ν i, lb ≤ φ ν i := fun ν i => by
    rw [hlb_def]; exact (phi_core hm Edges B C cl hN φ hrun.2.2.1 hrun.2.2.2.2.1 ν i).1
  have hφ0 := hrun.2.2.1
  have hφs := hrun.2.2.2.2.1
  have hsqn : ∀ v : Fin m → E d, 0 ≤ sqn v := fun v => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsc : 1 - lam > 0 := by linarith
  -- generic consequence of `ps_bound`
  have key : ∀ (v : ℕ → Fin m → E d) (e : ℕ → Fin m → E d),
      (∀ t i, φ (t + 1) i • v (t + 1) i = ∑ j, C t i j • (φ t j • v t j + e t j)) →
      sqn (wperp (φ ν) (v ν)) ≤ 2 * m * Kc ^ 2 * (lam ^ (2 * ν) * (m * sqn (wperp (φ 0) (v 0))) +
        lam / (1 - lam) * ∑ t ∈ Finset.range ν, lam ^ (ν - t) * (m * sqn (e t))) := by
    intro v e hv
    have hb := fun i => ps_bound hm0 C hC hcol φ hφ0 hφs (fun t i => φ t i • v t i) e hv
      lb Cc lam hlb0 hlb hsp ν i
    have hw : ∀ i, ‖wperp (φ ν) (v ν) i‖ ≤ Kc * (lam ^ ν * ∑ j, ‖wperp (φ 0) (v 0) j‖ +
        ∑ t ∈ Finset.range ν, lam ^ (ν - t) * ∑ j, ‖e t j‖) := by
      intro i
      have h := hb i
      have e1 : (φ ν i)⁻¹ • (φ ν i • v ν i) - (1 / (m : ℝ)) • ∑ j, φ ν j • v ν j =
          wperp (φ ν) (v ν) i := by
        rw [inv_smul_smul₀ (hpos ν i).ne']; rfl
      have e2 : ∀ j, φ 0 j • v 0 j - (1 / (m : ℝ)) • ∑ l, φ 0 l • v 0 l = wperp (φ 0) (v 0) j := by
        intro j; rw [hφ0 j, one_smul]; rfl
      simp only [e1, e2] at h
      rw [hK_def]; exact h
    have hsb := sq_bound (wperp (φ ν) (v ν)) Kc lam (∑ j, ‖wperp (φ 0) (v 0) j‖) ν
      (fun t => ∑ j, ‖e t j‖) hK0.le hl0 hl1 (Finset.sum_nonneg fun j _ => norm_nonneg _)
      (fun t => Finset.sum_nonneg fun j _ => norm_nonneg _) hw
    refine hsb.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hA0 := sum_norm_sq_le (wperp (φ 0) (v 0))
    have hE : ∑ t ∈ Finset.range ν, lam ^ (ν - t) * (∑ j, ‖e t j‖) ^ 2 ≤
        ∑ t ∈ Finset.range ν, lam ^ (ν - t) * (m * sqn (e t)) :=
      Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (sum_norm_sq_le (e t)) (pow_nonneg hl0.le _)
    have := mul_le_mul_of_nonneg_left hA0 (pow_nonneg hl0.le (2 * ν))
    have := mul_le_mul_of_nonneg_left hE (div_nonneg hl0.le hsc.le)
    linarith
  constructor
  · -- (81a)
    have hv : ∀ t i, φ (t + 1) i • x (t + 1) i =
        ∑ j, C t i j • (φ t j • x t j + (fun t j => (α * φ t j) • dir x xh t j) t j) := by
      intro t i
      rw [hrun.2.2.2.2.2.1 t i, smul_inv_smul₀ (hpos (t + 1) i).ne']
      apply Finset.sum_congr rfl; intro j _
      simp only [xhalf, smul_add, smul_smul]; ring_nf
    have h := key x _ hv
    have hE : ∀ t, sqn (fun j => (α * φ t j) • dir x xh t j) ≤ α ^ 2 * (m ^ 2 * sqn (dir x xh t)) := by
      intro t; unfold sqn
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro j _
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
      have : φ t j ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (hpos t j).le (hφm t j) 2
      have := mul_le_mul_of_nonneg_right this (sq_nonneg ‖dir x xh t j‖)
      nlinarith [sq_nonneg α]
    refine h.trans ?_
    have hS : ∑ t ∈ Finset.range ν, lam ^ (ν - t) * (m * sqn (fun j => (α * φ t j) • dir x xh t j)) ≤
        lam * ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (m ^ 3 * (α ^ 2 * sqn (dir x xh t))) := by
      rw [← shift_sum]
      apply Finset.sum_le_sum; intro t _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl0.le _)
      have := mul_le_mul_of_nonneg_left (hE t) (by positivity : (0:ℝ) ≤ m)
      nlinarith
    have hT0 : 0 ≤ ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) :=
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hl0.le _) (mul_nonneg (sq_nonneg _) (hsqn _))
    have e3 : ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (m ^ 3 * (α ^ 2 * sqn (dir x xh t))) =
        m ^ 3 * ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
    rw [e3] at hS
    have hS0 := hsqn (wperp (φ 0) (x 0))
    have hm4 : (m : ℝ) ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hmR (by norm_num)
    have hp2 : 0 ≤ lam ^ (2 * ν) := pow_nonneg hl0.le _
    have f1 : 2 * m * Kc ^ 2 * (lam ^ (2 * ν) * (m * sqn (wperp (φ 0) (x 0)))) ≤
        2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (x 0)) := by
      have : 2 * m * Kc ^ 2 * (lam ^ (2 * ν) * (m * sqn (wperp (φ 0) (x 0)))) =
          (2 * Kc ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (x 0))) * m ^ 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hm4
        (by positivity : (0:ℝ) ≤ 2 * Kc ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (x 0)))
      linarith
    have f2 : 2 * m * Kc ^ 2 * (lam / (1 - lam) *
        ∑ t ∈ Finset.range ν, lam ^ (ν - t) * (m * sqn (fun j => (α * φ t j) • dir x xh t j))) ≤
        2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 / (1 - lam) *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) := by
      have hc : 0 ≤ 2 * m * Kc ^ 2 * (lam / (1 - lam)) := by positivity
      have := mul_le_mul_of_nonneg_left hS hc
      have e : 2 * m * Kc ^ 2 * (lam / (1 - lam)) * (lam * (m ^ 3 *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)))) =
          2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 / (1 - lam) *
            ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) := by
        ring
      rw [e] at this
      linarith
    linarith
  · -- (81b)
    have hv : ∀ t i, φ (t + 1) i • y (t + 1) i =
        ∑ j, C t i j • (φ t j • y t j +
          (fun t j => gradient (f j) (x (t + 1) j) - gradient (f j) (x t j)) t j) := by
      intro t i
      rw [hrun.2.2.2.2.2.2 t i, smul_inv_smul₀ (hpos (t + 1) i).ne']
      apply Finset.sum_congr rfl; intro j _
      rw [add_sub_assoc]
    have h := key y _ hv
    have hE : ∀ t, sqn (fun j => gradient (f j) (x (t + 1) j) - gradient (f j) (x t j)) ≤
        Lmx Li ^ 2 * ((m : ℝ) ^ 2 * (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t))) := by
      intro t
      have hdx := dx_bound hN hα0 hrun t
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hdx (sq_nonneg _))
      unfold sqn
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j _
      have hl := grad_lip hA h1 j (hxK (t + 1) j) (hxK t j)
      have hLj : Li j ≤ Lmx Li := le_ciSup (Set.finite_range Li).bddAbove j
      have h2 : ‖gradient (f j) (x (t + 1) j) - gradient (f j) (x t j)‖ ≤
          Lmx Li * ‖x (t + 1) j - x t j‖ :=
        hl.trans (mul_le_mul_of_nonneg_right hLj (norm_nonneg _))
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [mul_pow] at this; exact this
    refine h.trans ?_
    set Q : ℕ → ℝ := fun t => 8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)
    have hQ0 : ∀ t, 0 ≤ Q t := fun t => by
      have := hsqn (wperp (φ t) (x t)); have := hsqn (dir x xh t); simp only [Q]; positivity
    have hS : ∑ t ∈ Finset.range ν, lam ^ (ν - t) *
        (m * sqn (fun j => gradient (f j) (x (t + 1) j) - gradient (f j) (x t j))) ≤
        lam * (m ^ 3 * Lmx Li ^ 2 * ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t) := by
      have hpt : ∀ t ∈ Finset.range ν, lam ^ (ν - t) *
          (m * sqn (fun j => gradient (f j) (x (t + 1) j) - gradient (f j) (x t j))) ≤
          (m : ℝ) ^ 3 * Lmx Li ^ 2 * (lam ^ (ν - t) * Q t) := by
        intro t _
        have := mul_le_mul_of_nonneg_left (hE t) (by positivity : (0:ℝ) ≤ m)
        have hp := pow_nonneg hl0.le (ν - t)
        have h2 := mul_le_mul_of_nonneg_left this hp
        have e : lam ^ (ν - t) * (m * (Lmx Li ^ 2 * ((m : ℝ) ^ 2 * Q t))) =
            (m : ℝ) ^ 3 * Lmx Li ^ 2 * (lam ^ (ν - t) * Q t) := by ring
        linarith
      refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, shift_sum]; ring
    have hSum0 : 0 ≤ ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t :=
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hl0.le _) (hQ0 t)
    have hS0 := hsqn (wperp (φ 0) (y 0))
    have hm4 : (m : ℝ) ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hmR (by norm_num)
    have f1 : 2 * m * Kc ^ 2 * (lam ^ (2 * ν) * (m * sqn (wperp (φ 0) (y 0)))) ≤
        2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (y 0)) := by
      have : 2 * m * Kc ^ 2 * (lam ^ (2 * ν) * (m * sqn (wperp (φ 0) (y 0)))) =
          (2 * Kc ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (y 0))) * m ^ 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hm4
        (by positivity : (0:ℝ) ≤ 2 * Kc ^ 2 * lam ^ (2 * ν) * sqn (wperp (φ 0) (y 0)))
      linarith
    have hml : (1 : ℝ) ≤ m / lb ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : lb ^ 2 ≤ 1 := pow_le_one₀ hlb0.le hlb1
      linarith
    have f2 : 2 * m * Kc ^ 2 * (lam / (1 - lam) * ∑ t ∈ Finset.range ν, lam ^ (ν - t) *
        (m * sqn (fun j => gradient (f j) (x (t + 1) j) - gradient (f j) (x t j)))) ≤
        2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 * m * Lmx Li ^ 2 / (lb ^ 2 * (1 - lam)) *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t := by
      have hc : 0 ≤ 2 * m * Kc ^ 2 * (lam / (1 - lam)) := by positivity
      have := mul_le_mul_of_nonneg_left hS hc
      have e : 2 * m * Kc ^ 2 * (lam / (1 - lam)) * (lam * (m ^ 3 * Lmx Li ^ 2 *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t)) =
          (2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 * Lmx Li ^ 2 / (1 - lam) *
            ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t) * 1 := by
        ring
      have e2 : 2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 * m * Lmx Li ^ 2 / (lb ^ 2 * (1 - lam)) *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t =
          (2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 * Lmx Li ^ 2 / (1 - lam) *
            ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t) * (m / lb ^ 2) := by
        have hne1 : lb ≠ 0 := hlb0.ne'
        have hne2 : 1 - lam ≠ 0 := hsc.ne'
        field_simp
      have hX0 : 0 ≤ 2 * ((m : ℝ) ^ 2 * Kc) ^ 2 * lam ^ 2 * Lmx Li ^ 2 / (1 - lam) *
          ∑ t ∈ Finset.range ν, lam ^ (ν - 1 - t) * Q t :=
        mul_nonneg (div_nonneg (by positivity) hsc.le) hSum0
      rw [e] at this; rw [e2]
      have := mul_le_mul_of_nonneg_left hml hX0
      linarith
    rw [← hlb_def, mul_add]
    exact add_le_add f1 f2

end SPushAux

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li) :
    ∃ c0 ρB : ℝ, 0 < c0 ∧ 0 < ρB ∧ ρB < 1 ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ x y xh : ℕ → Fin m → SONATA.Undir.E d, ∀ φ : ℕ → Fin m → ℝ, IsRun K f G ft C α x y xh φ →
      ∀ ν : ℕ,
        sqn (wperp (φ ν) (x ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (x 0))
              + 2 * c0 ^ 2 * ρB ^ 2 / (1 - ρB) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) ∧
        sqn (wperp (φ ν) (y ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (y 0))
              + 2 * c0 ^ 2 * ρB ^ 2 * m * SONATA.Undir.Lmx Li ^ 2 / (phiLb m B cl ^ 2 * (1 - ρB)) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) *
                    (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- one agent: the weighted consensus errors vanish
    have hm0 : 0 < m := hP.1
    refine ⟨1, 1 / 2, one_pos, by norm_num, by norm_num, ?_⟩
    intro α hα0 hα1 x y xh φ hrun ν
    have hm1 : m = 1 := by omega
    subst hm1
    have hcol := hN.2.2.2.2
    have hC1 : ∀ ν, C ν 0 0 = 1 := fun ν => by simpa using hcol ν 0
    have hφ1 : ∀ ν j, φ ν j = 1 := by
      intro ν; induction ν with
      | zero => exact hrun.2.2.1
      | succ n ih => intro j; rw [hrun.2.2.2.2.1 n j]; simp [Fin.fin_one_eq_zero j, hC1, ih]
    have hw : ∀ t (v : Fin 1 → SONATA.Undir.E d), sqn (wperp (φ t) v) = 0 := by
      intro t v; unfold sqn; simp [wperp, wavg, hφ1]
    have hsqn : ∀ v : Fin 1 → SONATA.Undir.E d, 0 ≤ sqn v := fun v =>
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hlb : 0 < phiLb 1 B cl := by simp [phiLb]
    simp only [hw, mul_zero, zero_add]
    constructor
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity)
        (mul_nonneg (sq_nonneg _) (hsqn _))
    · apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity)
        (mul_nonneg (by positivity) (hsqn _))
  · exact SPushAux.L42_main hm K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN μi Li h1
