-- Prove2me | solution 1 for RamseyDisambig.Spherical.lemma_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.588992+00:00
-- url     : https://prove2.me/submissions/8c103c5a-c30b-402c-90b8-6f6bbb46c476
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring
import Definitions.Def_RamseyDisambig_Spherical_Torus
import Definitions.Def_RamseyDisambig_Spherical_BlockMaps
import Theorems.Thm_RamseyDisambig_Spherical_theorem_11

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Pullback

open RamseyDisambig.Spherical

theorem le_finiteDiameter {X : Type*} [Finite X] (d : X → X → ℝ) (x y : X) :
    d x y ≤ finiteDiameter d := by
  unfold finiteDiameter
  haveI : Finite (X × X) := inferInstance
  exact le_csSup (Set.finite_range _).bddAbove ⟨(x, y), rfl⟩

theorem exists_eq_finiteDiameter {X : Type*} [Finite X] [Nonempty X] (d : X → X → ℝ) :
    ∃ x y, d x y = finiteDiameter d := by
  unfold finiteDiameter
  have hne : (Set.range (fun p : X × X => d p.1 p.2)).Nonempty := ⟨_, ⟨(Classical.arbitrary X, Classical.arbitrary X), rfl⟩⟩
  obtain ⟨⟨x, y⟩, h⟩ := Set.Nonempty.csSup_mem hne (Set.finite_range _)
  exact ⟨x, y, h⟩

/-- Lemma 9 for arbitrary nonnegative distance functions. -/
theorem pullback_gap {X Y : Type*} [Finite X] [Finite Y] (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (dX : X → X → ℝ) (dY : Y → Y → ℝ) (hY : ∀ y y', 0 ≤ dY y y')
    (ι₁ ι₂ : Y → X) (scale Δ : ℝ) (hscale0 : 0 ≤ scale) (hΔ : 0 ≤ Δ)
    (hscale : ∀ y y', dX (ι₁ y) (ι₂ y') = scale * dY y y' + Δ)
    (c : X → X → Bool) (hc : GapColoring ε dX c)
    (hdiam : (1 - ε / 2) * finiteDiameter dX ≤ scale * finiteDiameter dY) :
    GapColoring (ε / 2) dY (fun y y' => c (ι₁ y) (ι₂ y')) := by
  constructor
  all_goals intro y y' h
  all_goals
    have hYne : Nonempty Y := ⟨y⟩
    obtain ⟨u, v, huv⟩ := exists_eq_finiteDiameter dY
    have h1 : scale * finiteDiameter dY + Δ ≤ finiteDiameter dX := by
      rw [← huv, ← hscale]; exact le_finiteDiameter dX _ _
    have hDX : 0 ≤ finiteDiameter dX := by
      have := le_finiteDiameter dX (ι₁ y) (ι₂ y'); rw [hscale] at this
      have := hY y y'; nlinarith [hscale0, hΔ, mul_nonneg hscale0 (hY y y')]
    have hΔle : Δ ≤ ε / 2 * finiteDiameter dX := by nlinarith
  · apply hc.1
    rw [hscale]
    have : scale * dY y y' ≤ scale * (ε / 2 * finiteDiameter dY) := mul_le_mul_of_nonneg_left h hscale0
    nlinarith
  · apply hc.2
    rw [hscale]
    have : scale * ((1 - ε / 2) * finiteDiameter dY) ≤ scale * dY y y' :=
      mul_le_mul_of_nonneg_left h hscale0
    have h2 : (1 - ε / 2) * ((1 - ε / 2) * finiteDiameter dX) ≤ (1 - ε / 2) * (scale * finiteDiameter dY) :=
      mul_le_mul_of_nonneg_left hdiam (by linarith)
    nlinarith [mul_nonneg hε.le hDX]

end RamseyDisambig.Dev.Pullback
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L12

open RamseyDisambig.Spherical DihedralGroup

/-- Action of the dihedral group on `ZMod n`: `r i • x = x - i`, `sr i • x = i - x`. -/
instance instSMul (n : ℕ) : SMul (DihedralGroup n) (ZMod n) where
  smul g x := match g with
    | r i => x - i
    | sr i => i - x

@[simp] theorem r_smul {n : ℕ} (i x : ZMod n) : (r i : DihedralGroup n) • x = x - i := rfl
@[simp] theorem sr_smul {n : ℕ} (i x : ZMod n) : (sr i : DihedralGroup n) • x = i - x := rfl

instance instMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  one_smul x := by
    have : (1 : DihedralGroup n) = r 0 := one_def
    rw [this]; exact sub_zero x
  mul_smul g h x := by
    rcases g with i | i <;> rcases h with j | j <;> simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;> ring

/-- Sign homomorphism. -/
def signHom (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun g := match g with
    | r _ => 1
    | sr _ => Multiplicative.ofAdd 1
  map_one' := by rw [one_def]
  map_mul' g h := by
    rcases g with i | i <;> rcases h with j | j <;> simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr]
    · rw [← ofAdd_add]; decide

def rotHom (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := r i.toAdd
  map_one' := by simp [r_zero]
  map_mul' i j := by simp [r_mul_r]

instance isSolvable (n : ℕ) : Group.IsSolvable (DihedralGroup n) := by
  refine Group.isSolvable_of_ker_le_range (rotHom n) (signHom n) ?_
  intro g hg
  rcases g with i | i
  · exact ⟨Multiplicative.ofAdd i, rfl⟩
  · exfalso
    have : signHom n (sr i) = 1 := hg
    simp [signHom] at this


section dist
variable {R : ℕ+}

/-- `f t = min (t.val) (R - t.val)`. -/
def fd (t : ZMod (R : ℕ)) : ℝ := min ((t.val : ℝ)) ((R : ℝ) - t.val)

theorem cd_eq (x y : ZMod (R : ℕ)) : cyclicDistance x y = fd (x - y) := by
  unfold cyclicDistance fd
  rcases le_or_gt y.val x.val with h | h
  · have h' : (y.val : ℝ) ≤ x.val := by exact_mod_cast h
    rw [ZMod.val_sub h, Nat.cast_sub h, abs_of_nonneg (by linarith)]
  · have hne : y - x ≠ 0 := by
      intro h0
      have := ZMod.val_sub h.le
      rw [h0, ZMod.val_zero] at this
      omega
    have e : x - y = -(y - x) := by ring
    rw [e, ZMod.neg_val, if_neg hne, ZMod.val_sub h.le, Nat.cast_sub (by have := ZMod.val_lt y; omega),
      Nat.cast_sub h.le,
      abs_of_nonpos (by have : (x.val : ℝ) < y.val := by exact_mod_cast h
                        linarith)]
    rw [min_comm]; congr 1 <;> ring

theorem fd_nonneg (t : ZMod (R : ℕ)) : 0 ≤ fd t := by
  unfold fd
  have : (t.val : ℝ) < R := by exact_mod_cast ZMod.val_lt t
  exact le_min (by positivity) (by linarith)

theorem cd_nonneg (x y : ZMod (R : ℕ)) : 0 ≤ cyclicDistance x y := by
  rw [cd_eq]; exact fd_nonneg _

theorem fd_neg (t : ZMod (R : ℕ)) : fd (-t) = fd t := by
  unfold fd
  by_cases h : t = 0
  · subst h; simp
  · rw [ZMod.neg_val, if_neg h, Nat.cast_sub (ZMod.val_lt t).le]
    rw [min_comm]; congr 1; ring

theorem cd_smul (g : DihedralGroup (R : ℕ)) (a b : ZMod (R : ℕ)) :
    cyclicDistance (g • a) (g • b) = cyclicDistance a b := by
  rw [cd_eq, cd_eq]
  rcases g with i | i
  · simp
  · simp only [sr_smul]
    have : i - a - (i - b) = -(a - b) := by ring
    rw [this, fd_neg]

theorem fd_eq_cases (t t' : ZMod (R : ℕ)) (h : fd t = fd t') : t' = t ∨ t' = -t := by
  have h1 : (t.val : ℝ) < R := by exact_mod_cast ZMod.val_lt t
  have h2 : (t'.val : ℝ) < R := by exact_mod_cast ZMod.val_lt t'
  have key : (t.val : ℝ) = t'.val ∨ (t.val : ℝ) + t'.val = R := by
    unfold fd at h
    rcases min_choice (t.val : ℝ) (R - t.val) with e | e <;>
    rcases min_choice (t'.val : ℝ) (R - t'.val) with e' | e' <;>
    rw [e, e'] at h
    · left; exact h
    · right; linarith
    · right; linarith
    · left; linarith
  rcases key with k | k
  · left; exact ZMod.val_injective _ (by exact_mod_cast k.symm)
  · right
    have hne : t ≠ 0 := by
      intro h0
      have : (t.val : ℝ) = 0 := by simp [h0]
      linarith
    apply ZMod.val_injective
    rw [ZMod.neg_val, if_neg hne]
    have : (t.val + t'.val : ℕ) = R := by exact_mod_cast k
    omega

theorem exists_smul_eq (a b a' b' : ZMod (R : ℕ)) (h : cyclicDistance a b = cyclicDistance a' b') :
    ∃ g : DihedralGroup (R : ℕ), g • a = a' ∧ g • b = b' := by
  rw [cd_eq, cd_eq] at h
  rcases fd_eq_cases _ _ h with e | e
  · refine ⟨r (a - a'), by simp, ?_⟩
    simp
    linear_combination e
  · refine ⟨sr (a + a'), by simp, ?_⟩
    simp
    linear_combination e

end dist

end RamseyDisambig.Dev.L12
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L12

open RamseyDisambig.Spherical RamseyDisambig.Dev.Pullback

section diam
variable {R : ℕ+}

theorem torusDistance_nonneg {n : ℕ} (x y : Torus R n) : 0 ≤ torusDistance x y :=
  Finset.sum_nonneg fun _ _ => cd_nonneg _ _

theorem diam_torus (n : ℕ) :
    finiteDiameter (torusDistance : Torus R n → Torus R n → ℝ) =
      n * finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ) := by
  apply le_antisymm
  · unfold finiteDiameter
    refine csSup_le ⟨_, ⟨(0, 0), rfl⟩⟩ ?_
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have : torusDistance x y ≤ ∑ _i : Fin n, finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ) :=
      Finset.sum_le_sum fun i _ => le_finiteDiameter _ _ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · obtain ⟨a, b, hab⟩ := exists_eq_finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ)
    have := le_finiteDiameter (torusDistance : Torus R n → Torus R n → ℝ) (fun _ => a) (fun _ => b)
    have e : torusDistance (fun _ : Fin n => a) (fun _ => b) = n * cyclicDistance a b := by
      simp [torusDistance, distanceProfile]
    rw [e, hab] at this
    exact this

end diam

section block
variable {R : ℕ+} {n N : ℕ}

abbrev XX (R : ℕ+) := ZMod (R : ℕ) × ZMod (R : ℕ)

def i1 (φ : (Fin n → XX R) → (Fin N → XX R)) (x : Torus R n) : Torus R N :=
  fun ℓ => (φ (fun j => (x j, 0)) ℓ).1

def i2 (φ : (Fin n → XX R) → (Fin N → XX R)) (y : Torus R n) : Torus R N :=
  fun ℓ => (φ (fun j => (0, y j)) ℓ).2

variable (φ : (Fin n → XX R) → (Fin N → XX R)) (I : Fin n → Finset (Fin N))
  (γ : Fin N → DihedralGroup (R : ℕ)) (z : {ℓ : Fin N // ∀ j, ℓ ∉ I j} → XX R)
  (hblk : ∀ x j ℓ, ℓ ∈ I j → φ x ℓ = γ ℓ • x j)
  (hfix : ∀ x ℓ (h : ∀ j, ℓ ∉ I j), φ x ℓ = z ⟨ℓ, h⟩)

include hblk in
theorem i1_block (x : Torus R n) (j : Fin n) (ℓ : Fin N) (h : ℓ ∈ I j) :
    i1 φ x ℓ = γ ℓ • x j := by
  simp [i1, hblk _ _ _ h]

include hblk in
theorem i2_block (x : Torus R n) (j : Fin n) (ℓ : Fin N) (h : ℓ ∈ I j) :
    i2 φ x ℓ = γ ℓ • x j := by
  simp [i2, hblk _ _ _ h]

include hfix in
theorem i1_fix (x : Torus R n) (ℓ : Fin N) (h : ∀ j, ℓ ∉ I j) :
    i1 φ x ℓ = (z ⟨ℓ, h⟩).1 := by
  simp [i1, hfix _ _ h]

include hfix in
theorem i2_fix (x : Torus R n) (ℓ : Fin N) (h : ∀ j, ℓ ∉ I j) :
    i2 φ x ℓ = (z ⟨ℓ, h⟩).2 := by
  simp [i2, hfix _ _ h]

include hblk hfix in
theorem phi_split (x y : Torus R n) :
    φ (fun j => (x j, y j)) = fun ℓ => (i1 φ x ℓ, i2 φ y ℓ) := by
  funext ℓ
  by_cases h : ∃ j, ℓ ∈ I j
  · obtain ⟨j, hj⟩ := h
    rw [hblk _ _ _ hj, i1_block φ I γ hblk _ j ℓ hj, i2_block φ I γ hblk _ j ℓ hj]
    rfl
  · push Not at h
    rw [hfix _ _ h, i1_fix φ I z hfix _ _ h, i2_fix φ I z hfix _ _ h]

include hblk hfix in
theorem dist_formula (hdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j)) (k : ℕ)
    (hcard : ∀ i, (I i).card = k) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ x y : Torus R n,
      torusDistance (i1 φ x) (i2 φ y) = k * torusDistance x y + Δ := by
  classical
  let U : Finset (Fin N) := Finset.univ.biUnion I
  refine ⟨∑ ℓ ∈ Uᶜ, cyclicDistance (i1 φ (fun _ => 0) ℓ) (i2 φ (fun _ => 0) ℓ),
    Finset.sum_nonneg fun _ _ => cd_nonneg _ _, fun x y => ?_⟩
  unfold torusDistance distanceProfile
  rw [← Finset.sum_add_sum_compl U]
  congr 1
  · rw [Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∑ ℓ ∈ I j, cyclicDistance (i1 φ x ℓ) (i2 φ y ℓ) =
        ∑ _ℓ ∈ I j, cyclicDistance (x j) (y j) := by
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      rw [i1_block φ I γ hblk x j ℓ hℓ, i2_block φ I γ hblk y j ℓ hℓ, cd_smul]
    rw [e]
    simp [hcard]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have h : ∀ j, ℓ ∉ I j := by
      intro j hj
      simp only [Finset.mem_compl, U, Finset.mem_biUnion, Finset.mem_univ, true_and] at hℓ
      exact hℓ ⟨j, hj⟩
    rw [i1_fix φ I z hfix x ℓ h, i1_fix φ I z hfix _ ℓ h, i2_fix φ I z hfix y ℓ h,
      i2_fix φ I z hfix _ ℓ h]

end block

end RamseyDisambig.Dev.L12
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L12

open RamseyDisambig.Spherical RamseyDisambig.Dev.Pullback

theorem main (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (R : ℕ+) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ c : Torus R N → Torus R N → Bool,
      GapColoring ε torusDistance c →
      ∃ ι₁ ι₂ : Torus R n → Torus R N,
        GapColoring (ε / 2) torusDistance (fun x y => c (ι₁ x) (ι₂ y)) ∧
        DistanceProfileCanonical (fun x y => c (ι₁ x) (ι₂ y)) := by
  obtain ⟨N, k, hN, hk, hdense, hall⟩ :=
    theorem_11 (DihedralGroup (R : ℕ)) (XX R) 2 n (by norm_num) hn (ε / 2) (by linarith)
      (by linarith)
  refine ⟨N, hN, fun c hc => ?_⟩
  obtain ⟨φ, ⟨I, hdisj, hcard, γ, z, hblk, hfix⟩, horb⟩ := hall
    (fun w => if c (fun ℓ => (w ℓ).1) (fun ℓ => (w ℓ).2) = true then 1 else 0)
  obtain ⟨Δ, hΔ, hd⟩ := dist_formula φ I γ z hblk hfix hdisj k hcard
  refine ⟨i1 φ, i2 φ, ?_, ?_⟩
  · refine pullback_gap ε hε hεhalf torusDistance torusDistance
      (fun y y' => torusDistance_nonneg y y') (i1 φ) (i2 φ) k Δ (by positivity) hΔ hd c hc ?_
    rw [diam_torus, diam_torus]
    have hD : 0 ≤ finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ) :=
      le_trans (cd_nonneg 0 0) (le_finiteDiameter _ _ _)
    nlinarith [mul_le_mul_of_nonneg_right hdense hD]
  · intro x y x' y' h
    have key := horb (fun j => (x j, y j)) (fun j => (x' j, y' j)) (fun j => by
      obtain ⟨g, hg1, hg2⟩ := exists_smul_eq (x j) (y j) (x' j) (y' j) (congrFun h j)
      exact ⟨g, by simp [hg1, hg2]⟩)
    rw [phi_split φ I γ z hblk hfix, phi_split φ I γ z hblk hfix] at key
    simp only at key
    cases h1 : c (i1 φ x) (i2 φ y) <;> cases h2 : c (i1 φ x') (i2 φ y') <;>
      simp_all

end RamseyDisambig.Dev.L12

namespace RamseyDisambig.Spherical

/-- Lemma 12, p. 11. All torus dimensions and side lengths are positive. -/
theorem chk_lemma_12 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (R : ℕ+) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ c : Torus R N → Torus R N → Bool,
      GapColoring ε torusDistance c →
      ∃ ι₁ ι₂ : Torus R n → Torus R N,
        GapColoring (ε / 2) torusDistance (fun x y => c (ι₁ x) (ι₂ y)) ∧
        DistanceProfileCanonical (fun x y => c (ι₁ x) (ι₂ y)) :=
  RamseyDisambig.Dev.L12.main ε hε hεhalf R n hn

end RamseyDisambig.Spherical

end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_lemma_12 := @RamseyDisambig.Spherical.chk_lemma_12
