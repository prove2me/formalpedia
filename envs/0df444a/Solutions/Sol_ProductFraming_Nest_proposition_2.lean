-- Prove2me | solution 1 for ProductFraming.Nest.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:22:35.761575+00:00
-- url     : https://prove2.me/submissions/6f8dd2a6-eb20-495e-a2af-9638307e6f0c

import Mathlib
import Definitions.Def_ProductFraming_Nest_Program

open Finset

namespace PFNProgAux

open ProductFraming.Nest

variable {m : ℕ} {L : ℕ → ℝ}

lemma L_anti (hL : Feasible6 m L) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ m) : L b ≤ L a := by
  have : ∀ d, ∀ b, b = a + d → b ≤ m → L b ≤ L a := by
    intro d
    induction d with
    | zero => intro b hb _; subst hb; exact le_refl _
    | succ d ih =>
      intro b hb hbm
      subst hb
      exact le_trans (hL.2.1 (a + d) (by omega) (by omega)) (ih (a + d) rfl (by omega))
  exact this (b - a) b (by omega) hb

lemma L_nonneg (hL : Feasible6 m L) {a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) : 0 ≤ L a :=
  le_trans hL.2.2.1 (L_anti hL ha ham le_rfl)

lemma L_le_one (hL : Feasible6 m L) {a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) : L a ≤ 1 :=
  hL.1 ▸ L_anti hL le_rfl ha ham

lemma lamOf_nonneg (hL : Feasible6 m L) {x : ℕ} (hx : x ∈ Finset.Icc 1 m) : 0 ≤ lamOf m L x := by
  rw [Finset.mem_Icc] at hx
  unfold lamOf
  split_ifs with h
  · linarith [hL.2.1 x hx.1 (by omega)]
  · linarith [L_nonneg hL hx.1 hx.2]

lemma EminTail_ge_one (hL : Feasible6 m L) {x : ℕ} (hx : x ∈ Finset.Icc 1 m) : 1 ≤ EminTail L x := by
  rw [Finset.mem_Icc] at hx
  unfold EminTail
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hx.1, sum_insert (by simp), hL.1]
  have : 0 ≤ ∑ y ∈ Finset.Icc (1 + 1) x, L y := by
    apply sum_nonneg; intro y hy; rw [Finset.mem_Icc] at hy
    exact L_nonneg hL (by omega) (by omega)
  linarith

lemma ratio6_nonneg (hL : Feasible6 m L) : 0 ≤ ratio6 m L := by
  unfold ratio6
  apply sum_nonneg
  intro x hx
  exact div_nonneg (mul_nonneg (lamOf_nonneg hL hx) (Nat.cast_nonneg x))
    (by linarith [EminTail_ge_one hL hx])

/-- Weak duality: `1 ≤ J5(U, Λ) · ratio6(Λ)` for every feasible `(U, Λ)`. -/
lemma weak_duality (hm : 1 ≤ m) {U : ℕ → ℝ} (hF : Feasible5 m U L) : 1 ≤ J5 hm U L * ratio6 m L := by
  have hL := hF.1
  have hUle : ∀ x ∈ Finset.Icc 1 m,
      lamOf m L x * U x ≤ J5 hm U L * (lamOf m L x * (x : ℝ) / EminTail L x) := by
    intro x hx
    have hEx := EminTail_ge_one hL hx
    have hx1 : (0 : ℝ) < x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
    have hle : U x / (x : ℝ) * EminTail L x ≤ J5 hm U L :=
      Finset.le_sup' (fun x => U x / (x : ℝ) * EminTail L x) hx
    have hU : U x ≤ J5 hm U L * x / EminTail L x := by
      rw [le_div_iff₀ (by linarith)]
      have : U x / (x : ℝ) * EminTail L x * x = U x * EminTail L x := by field_simp
      nlinarith
    calc lamOf m L x * U x ≤ lamOf m L x * (J5 hm U L * x / EminTail L x) :=
          mul_le_mul_of_nonneg_left hU (lamOf_nonneg hL hx)
      _ = J5 hm U L * (lamOf m L x * (x : ℝ) / EminTail L x) := by ring
  rw [← hF.2.2.2.1]
  unfold ratio6
  rw [mul_sum]
  exact sum_le_sum hUle

lemma J5_nonneg (hm : 1 ≤ m) {U : ℕ → ℝ} (hF : Feasible5 m U L) : 0 ≤ J5 hm U L := by
  have hx1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have := Finset.le_sup' (fun x => U x / (x : ℝ) * EminTail L x) hx1
  have h0 : 0 ≤ U 1 / ((1 : ℕ) : ℝ) * EminTail L 1 :=
    mul_nonneg (div_nonneg (hF.2.2.2.2 1 hx1) (Nat.cast_nonneg 1))
      (by linarith [EminTail_ge_one hF.1 hx1])
  exact le_trans h0 this

/-- Downward induction from `y` to `1`. -/
lemma down {y : ℕ} (Q : ℕ → Prop) (h0 : 1 ≤ y → Q y)
    (hs : ∀ x, 1 ≤ x → x < y → Q (x + 1) → Q x) : ∀ x, 1 ≤ x → x ≤ y → Q x := by
  have : ∀ d x, x + d = y → 1 ≤ x → Q x := by
    intro d
    induction d with
    | zero => intro x hx h1; subst hx; exact h0 (by simpa using h1)
    | succ d ih =>
      intro x hx h1
      exact hs x h1 (by omega) (ih (x + 1) (by omega) (by omega))
  intro x h1 h2
  exact this (y - x) x (by omega) h1

lemma sum_Icc_split (f : ℕ → ℝ) {x m : ℕ} (h : x ≤ m) :
    ∑ y ∈ Finset.Icc x m, f y = f x + ∑ y ∈ Finset.Icc (x + 1) m, f y := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, sum_insert]
  simp

lemma sum_lamOf_from : ∀ x, 1 ≤ x → x ≤ m → ∑ y ∈ Finset.Icc x m, lamOf m L y = L x := by
  apply down (y := m) (fun x => ∑ y ∈ Finset.Icc x m, lamOf m L y = L x)
  · intro _
    unfold lamOf
    simp
  · intro x hx hxm ih
    rw [sum_Icc_split _ hxm.le, ih]
    unfold lamOf
    rw [if_pos (by omega)]; ring

lemma sum_lamOf (hm : 1 ≤ m) (hL : Feasible6 m L) : ∑ y ∈ Finset.Icc 1 m, lamOf m L y = L 1 :=
  sum_lamOf_from 1 le_rfl hm

lemma ratio6_pos (hm : 1 ≤ m) (hL : Feasible6 m L) : 0 < ratio6 m L := by
  unfold ratio6
  apply sum_pos'
  · intro x hx
    exact div_nonneg (mul_nonneg (lamOf_nonneg hL hx) (Nat.cast_nonneg x))
      (by linarith [EminTail_ge_one hL hx])
  · -- `∑ λ(x) = Λ(1) = 1`, so some `λ(x) > 0`
    by_contra hcon
    push_neg at hcon
    have hz : ∀ x ∈ Finset.Icc 1 m, lamOf m L x = 0 := by
      intro x hx
      have h1 := hcon x hx
      have hE := EminTail_ge_one hL hx
      have hx1 : (0 : ℝ) < x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
      have h2 : lamOf m L x * x ≤ 0 := by
        have := (div_nonpos_iff.mp h1)
        rcases this with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · exact h
      have h3 := lamOf_nonneg hL hx
      nlinarith
    have h1 := sum_lamOf hm hL
    rw [sum_eq_zero hz, hL.1] at h1
    norm_num at h1

/-- The tail-function feasible for (6) from values on `[1, m]`. -/
noncomputable def ext (m : ℕ) (a : Fin m → ℝ) : ℕ → ℝ :=
  fun x => if h : 1 ≤ x ∧ x ≤ m then a ⟨x - 1, by omega⟩ else 0

lemma continuous_ext (x : ℕ) : Continuous (fun a : Fin m → ℝ => ext m a x) := by
  unfold ext
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma feasible6_congr {L L' : ℕ → ℝ} (hm : 1 ≤ m) (h : ∀ x, 1 ≤ x → x ≤ m → L x = L' x) :
    Feasible6 m L → Feasible6 m L' := by
  rintro ⟨h1, h2, h3, h4⟩
  have hs : ∀ a, 1 ≤ a → ∑ y ∈ Finset.Icc a m, L y = ∑ y ∈ Finset.Icc a m, L' y := by
    intro a ha; apply sum_congr rfl; intro y hy; rw [Finset.mem_Icc] at hy
    exact h y (by omega) hy.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h 1 le_rfl hm]; exact h1
  · intro x hx hxm
    rw [← h x hx hxm.le, ← h (x + 1) (by omega) hxm]; exact h2 x hx hxm
  · rw [← h m hm le_rfl]; exact h3
  · intro x hx hxm
    rw [← hs (x + 1) (by omega), ← hs 1 le_rfl, ← h (x + 1) (by omega) hxm]; exact h4 x hx hxm

lemma ratio6_congr {L L' : ℕ → ℝ} (h : ∀ x, 1 ≤ x → x ≤ m → L x = L' x) :
    ratio6 m L = ratio6 m L' := by
  unfold ratio6
  apply sum_congr rfl
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hl : lamOf m L x = lamOf m L' x := by
    unfold lamOf
    split_ifs with h'
    · rw [h x hx.1 hx.2, h (x + 1) (by omega) h']
    · rw [h x hx.1 hx.2]
  have he : EminTail L x = EminTail L' x := by
    unfold EminTail; apply sum_congr rfl; intro y hy; rw [Finset.mem_Icc] at hy
    exact h y hy.1 (by omega)
  rw [hl, he]

lemma ext_restrict (L : ℕ → ℝ) : ∀ x, 1 ≤ x → x ≤ m → ext m (fun i => L (i.1 + 1)) x = L x := by
  intro x hx hxm
  unfold ext
  rw [dif_pos ⟨hx, hxm⟩]
  show L (x - 1 + 1) = L x
  congr 1; omega

/-- The maximum of `ratio6` over (6) is attained. -/
lemma exists_max_ratio6 (hm : 1 ≤ m) :
    ∃ L : ℕ → ℝ, Feasible6 m L ∧ ∀ L' : ℕ → ℝ, Feasible6 m L' → ratio6 m L' ≤ ratio6 m L := by
  set K : Set (Fin m → ℝ) := {a | Feasible6 m (ext m a)} with hK
  have hKeq : K = {a | ext m a 1 = 1} ∩ {a | 0 ≤ ext m a m} ∩
      ⋂ x ∈ Finset.Ico 1 m, ({a | ext m a (x + 1) ≤ ext m a x} ∩
        {a | ∑ y ∈ Finset.Icc (x + 1) m, ext m a y ≤ ext m a (x + 1) * ∑ y ∈ Finset.Icc 1 m, ext m a y}) := by
    ext a
    simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_Ico, Feasible6]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3⟩, fun x hx => ⟨h2 x hx.1 hx.2, h4 x hx.1 hx.2⟩⟩
    · rintro ⟨⟨h1, h3⟩, h⟩
      exact ⟨h1, fun x hx hxm => (h x ⟨hx, hxm⟩).1, h3, fun x hx hxm => (h x ⟨hx, hxm⟩).2⟩
  have hclosed : IsClosed K := by
    rw [hKeq]
    refine ((isClosed_eq (continuous_ext 1) continuous_const).inter
      (isClosed_le continuous_const (continuous_ext m))).inter ?_
    refine isClosed_biInter fun x _ => ?_
    exact (isClosed_le (continuous_ext _) (continuous_ext _)).inter
      (isClosed_le (continuous_finset_sum _ fun y _ => continuous_ext y)
        ((continuous_ext _).mul (continuous_finset_sum _ fun y _ => continuous_ext y)))
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
    intro a ha
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 := L_nonneg ha (a := i.1 + 1) (by omega) (by omega)
    have h2 := L_le_one ha (a := i.1 + 1) (by omega) (by omega)
    have he : ext m a (i.1 + 1) = a i := by
      unfold ext; rw [dif_pos ⟨by omega, by omega⟩]
      exact congrArg a (Fin.ext (by simp))
    rw [he] at h1 h2
    rw [Real.norm_of_nonneg h1]; exact h2
  have hcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : K.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    have hc : ∀ x, 1 ≤ x → x ≤ m → ext m (fun _ => (1 : ℝ)) x = 1 := by
      intro x hx hxm; unfold ext; rw [dif_pos ⟨hx, hxm⟩]
    show Feasible6 m (ext m fun _ => 1)
    refine feasible6_congr hm (L := fun _ => 1) (fun x hx hxm => (hc x hx hxm).symm) ?_
    refine ⟨rfl, fun _ _ _ => le_rfl, zero_le_one, fun x hx hxm => ?_⟩
    simp only [one_mul, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : m + 1 - (x + 1) ≤ m + 1 - 1)
  have hcont : ContinuousOn (fun a => ratio6 m (ext m a)) K := by
    unfold ratio6
    apply continuousOn_finset_sum
    intro x hx
    apply ContinuousOn.div
    · apply Continuous.continuousOn
      apply Continuous.mul _ continuous_const
      unfold lamOf
      split_ifs
      · exact (continuous_ext x).sub (continuous_ext (x + 1))
      · exact (continuous_ext x).sub continuous_const
    · exact (continuous_finset_sum _ fun y _ => continuous_ext y).continuousOn
    · intro a ha
      have := EminTail_ge_one ha hx
      linarith
  obtain ⟨a, ha, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨ext m a, ha, fun L' hL' => ?_⟩
  have hmem : (fun i : Fin m => L' (i.1 + 1)) ∈ K := by
    show Feasible6 m (ext m _)
    exact feasible6_congr hm (fun x hx hxm => (ext_restrict L' x hx hxm).symm) hL'
  have := hmax hmem
  simp only at this
  rw [ratio6_congr (fun x hx hxm => (ext_restrict L' x hx hxm).symm)]
  exact this

/-- From a tail `Λ` feasible for (6), the revenue curve `U(x) = x / (E[min(X,x)] · ratio6(Λ))` is
feasible for (5) and makes `(U(x)/x) E[min(X, x)]` constant equal to `1 / ratio6(Λ)`. -/
lemma feasible5_of (hm : 1 ≤ m) (hL : Feasible6 m L) :
    Feasible5 m (fun x : ℕ => (x : ℝ) / (EminTail L x * ratio6 m L)) L ∧
    ∀ x ∈ Finset.Icc 1 m,
      (fun x : ℕ => (x : ℝ) / (EminTail L x * ratio6 m L)) x / (x : ℝ) * EminTail L x = 1 / ratio6 m L := by
  have hR := ratio6_pos hm hL
  have hEsucc : ∀ x, EminTail L (x + 1) = EminTail L x + L (x + 1) := by
    intro x; unfold EminTail; rw [Finset.sum_Icc_succ_top (by omega)]
  have hconst : ∀ x ∈ Finset.Icc 1 m,
      (fun x : ℕ => (x : ℝ) / (EminTail L x * ratio6 m L)) x / (x : ℝ) * EminTail L x = 1 / ratio6 m L := by
    intro x hx
    have hE := EminTail_ge_one hL hx
    have hx1 : (0 : ℝ) < x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
    simp only
    field_simp
  refine ⟨⟨hL, ?_, ?_, ?_, ?_⟩, hconst⟩
  · intro x hx hxm
    have hE := EminTail_ge_one hL (Finset.mem_Icc.mpr ⟨hx, hxm.le⟩)
    have hE' := EminTail_ge_one hL (Finset.mem_Icc.mpr ⟨by omega, hxm⟩)
    simp only
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- `x Λ(x+1) ≤ x Λ(x) ≤ E[min(X,x)]`
    have hxE : (x : ℝ) * L (x + 1) ≤ EminTail L x := by
      unfold EminTail
      have : ∑ _y ∈ Finset.Icc 1 x, L (x + 1) ≤ ∑ y ∈ Finset.Icc 1 x, L y := by
        apply sum_le_sum; intro y hy; rw [Finset.mem_Icc] at hy
        exact L_anti hL hy.1 (by omega) hxm
      simpa using this
    rw [hEsucc x]
    push_cast
    nlinarith
  · intro x hx hxm
    have hE := EminTail_ge_one hL (Finset.mem_Icc.mpr ⟨hx, hxm.le⟩)
    have hx1 : (0 : ℝ) < x := by exact_mod_cast hx
    have hL1 := L_nonneg hL (a := x + 1) (by omega) hxm
    simp only
    push_cast
    have hc : ∀ y : ℝ, y ≠ 0 → ∀ c : ℝ, y / c / y = 1 / c := by
      intro y hy c; field_simp
    rw [hc _ (by positivity : ((x : ℝ) + 1) ≠ 0), hc _ hx1.ne']
    apply one_div_le_one_div_of_le (by positivity)
    rw [hEsucc x]
    nlinarith
  · have : ∑ x ∈ Finset.Icc 1 m, lamOf m L x * (fun x : ℕ => (x : ℝ) / (EminTail L x * ratio6 m L)) x
        = ratio6 m L / ratio6 m L := by
      unfold ratio6
      rw [sum_div]
      apply sum_congr rfl
      intro x hx
      have hE := EminTail_ge_one hL hx
      simp only
      field_simp
    rw [this, div_self hR.ne']
  · intro x hx
    have hE := EminTail_ge_one hL hx
    exact div_nonneg (Nat.cast_nonneg x) (by positivity)

end PFNProgAux

namespace PFNProgAux
open ProductFraming.Nest
variable {m : ℕ}

lemma J5_const (hm : 1 ≤ m) {U L : ℕ → ℝ} {c : ℝ}
    (h : ∀ x ∈ Finset.Icc 1 m, U x / (x : ℝ) * EminTail L x = c) : J5 hm U L = c := by
  unfold J5
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun x hx => (h x hx).le
  · have hx1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
    rw [← h 1 hx1]
    exact Finset.le_sup' (fun x => U x / (x : ℝ) * EminTail L x) hx1

/-- The optimum of (5): `J5(U, Λ) ≥ 1 / R*` for all feasible points, with `R* = max ratio6`. -/
lemma J5_ge (hm : 1 ≤ m) {Ls : ℕ → ℝ} (hLs : Feasible6 m Ls)
    (hmax : ∀ L' : ℕ → ℝ, Feasible6 m L' → ratio6 m L' ≤ ratio6 m Ls) {U L : ℕ → ℝ}
    (hF : Feasible5 m U L) : 1 / ratio6 m Ls ≤ J5 hm U L := by
  have hR := ratio6_pos hm hLs
  have h1 := weak_duality hm hF
  have h2 := hmax L hF.1
  have hJ := J5_nonneg hm hF
  rw [div_le_iff₀ hR]
  nlinarith

end PFNProgAux

open ProductFraming.Nest PFNProgAux in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∃ U Λ : ℕ → ℝ, Feasible5 m U Λ ∧
      (∀ U' Λ' : ℕ → ℝ, Feasible5 m U' Λ' → J5 hm U Λ ≤ J5 hm U' Λ') ∧
      ∀ x ∈ Icc 1 m, U x / (x : ℝ) * EminTail Λ x = J5 hm U Λ := by
  obtain ⟨Ls, hLs, hmax⟩ := exists_max_ratio6 hm
  obtain ⟨hF, hc⟩ := feasible5_of hm hLs
  have hJ := J5_const hm hc
  refine ⟨_, Ls, hF, fun U' L' hF' => ?_, fun x hx => ?_⟩
  · rw [hJ]; exact J5_ge hm hLs hmax hF'
  · rw [hJ]; exact hc x hx
