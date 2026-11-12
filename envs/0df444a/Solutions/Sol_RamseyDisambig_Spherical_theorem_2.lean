-- Prove2me | solution 1 for RamseyDisambig.Spherical.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.575963+00:00
-- url     : https://prove2.me/submissions/3f1d2c9c-46c7-4893-a98f-5aa3ee096a38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_RamseyDisambig_Spherical_Torus
import Definitions.Def_RamseyDisambig_Spherical_BlockMaps
import Definitions.Def_RamseyDisambig_Spherical_Cube
import Theorems.Thm_RamseyDisambig_Spherical_theorem_13

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

namespace RamseyDisambig.Dev.Basics

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

/-- If `q ≤ vcDim Q` then some `q` points are shattered. -/
theorem exists_shattered_of_le_vcDim {Z Λ : Type*} (Q : Λ → Z → Bool) (q : ℕ) (hq1 : 1 ≤ q)
    (h : (q : ℕ∞) ≤ vcDim Q) : ∃ z : Fin q → Z, Shatters Q z := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ (h' : ℕ), (∃ z : Fin h' → Z, Shatters Q z) → h' < q := by
    intro h' ⟨z, hz⟩
    by_contra hlt
    push_neg at hlt
    apply hcon (fun i => z (Fin.castLE hlt i))
    intro δ
    obtain ⟨α, hα⟩ := hz (fun j => if hj : (j : ℕ) < q then δ ⟨j, hj⟩ else false)
    refine ⟨α, fun i => ?_⟩
    have := hα (Fin.castLE hlt i)
    simpa using this
  have hle : vcDim Q ≤ ((q - 1 : ℕ) : ℕ∞) := by
    unfold vcDim
    refine iSup₂_le fun h' hh' => ?_
    have := key h' hh'
    exact_mod_cast Nat.le_sub_one_of_lt this
  have hq : (q : ℕ∞) ≤ ((q - 1 : ℕ) : ℕ∞) := h.trans hle
  have hq' : q ≤ q - 1 := by exact_mod_cast hq
  omega

/-- Shattered family gives vcDim ≥ its size. -/
theorem le_vcDim_of_shatters {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z)
    (hz : Shatters Q z) : (h : ℕ∞) ≤ vcDim Q := by
  unfold vcDim
  exact le_iSup₂_of_le h ⟨z, hz⟩ le_rfl

end RamseyDisambig.Dev.Basics
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L10

open NatureSLT.GrowthFunction

/-- Pullback form usable with `q = 0`-free hypothesis. -/
theorem vcDim_pullback {X Y : Type*} (ι₁ ι₂ : Y → X) (c : X → X → Bool)
    (q : ℕ) (hq : 1 ≤ q)
    (hvc : (q : ℕ∞) ≤ vcDim (fun y y' => c (ι₁ y) (ι₂ y'))) :
    (q : ℕ∞) ≤ vcDim c := by
  obtain ⟨z, hz⟩ := Basics.exists_shattered_of_le_vcDim _ q hq hvc
  refine Basics.le_vcDim_of_shatters c (fun i => ι₂ (z i)) ?_
  intro δ
  obtain ⟨α, hα⟩ := hz δ
  exact ⟨ι₁ α, hα⟩

end RamseyDisambig.Dev.L10

namespace RamseyDisambig.Spherical

end RamseyDisambig.Spherical
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

variable (I : Fin n → Finset (Fin N)) (γ : Fin N → DihedralGroup (R : ℕ))

end block

end RamseyDisambig.Dev.L12
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Thm2

open RamseyDisambig.Spherical RamseyDisambig.Dev.Pullback

/-- cycle embedding bit -/
def ph (r t : ℕ) (i : Fin r) : Bool := decide ((i : ℕ) < t ∧ t ≤ (i : ℕ) + r)

def D (r s t : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin r => ph r s i ≠ ph r t i).card

theorem card_fin_filter (q : ℕ → Prop) [DecidablePred q] (r : ℕ) :
    (Finset.univ.filter fun i : Fin r => q i).card = ((Finset.range r).filter q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if q i then 1 else 0) r

theorem D_eq_range (r s t : ℕ) :
    D r s t = ((Finset.range r).filter fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r))).card := by
  unfold D
  rw [← card_fin_filter (fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r)))]
  congr 1
  ext i
  simp only [ph, ne_eq, decide_eq_decide, Finset.mem_filter, Finset.mem_univ, true_and]

theorem D_comm (r s t : ℕ) : D r s t = D r t s := by
  rw [D_eq_range, D_eq_range]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  tauto

theorem D_eq (r s t : ℕ) (hs : s < 2 * r) (ht : t < 2 * r) (hst : s ≤ t) :
    D r s t = if t - s ≤ r then t - s else 2 * r - (t - s) := by
  rw [D_eq_range]
  by_cases h1 : t ≤ r
  · have : (Finset.range r).filter (fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r))) = Finset.Ico s t := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico]
    rw [if_pos (by omega)]
  · by_cases h2 : s ≤ r
    · by_cases h3 : s ≤ t - r
      · have : (Finset.range r).filter (fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r))) =
            Finset.Ico 0 s ∪ Finset.Ico (t - r) r := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Finset.mem_union]; omega
        rw [this, Finset.card_union_of_disjoint (Finset.disjoint_left.2 (by intro a; simp only [Finset.mem_Ico]; omega))]
        simp only [Nat.card_Ico]
        split_ifs <;> omega
      · have : (Finset.range r).filter (fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r))) =
            Finset.Ico 0 (t - r) ∪ Finset.Ico s r := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Finset.mem_union]; omega
        rw [this, Finset.card_union_of_disjoint (Finset.disjoint_left.2 (by intro a; simp only [Finset.mem_Ico]; omega))]
        simp only [Nat.card_Ico]
        split_ifs <;> omega
    · have : (Finset.range r).filter (fun i => ¬((i < s ∧ s ≤ i + r) ↔ (i < t ∧ t ≤ i + r))) =
          Finset.Ico (s - r) (t - r) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]
      split_ifs <;> omega

theorem cd_eq_D {R : ℕ+} (r : ℕ) (hR : (R : ℕ) = 2 * r) (s t : ZMod (R : ℕ)) :
    cyclicDistance s t = (D r s.val t.val : ℝ) := by
  have hs : s.val < 2 * r := hR ▸ ZMod.val_lt s
  have ht : t.val < 2 * r := hR ▸ ZMod.val_lt t
  have hRr : ((R : ℕ) : ℝ) = 2 * r := by exact_mod_cast hR
  unfold cyclicDistance
  have key : ∀ a b : ℕ, a < 2 * r → b < 2 * r → a ≤ b →
      min (|(a : ℝ) - b|) (((R : ℕ) : ℝ) - |(a : ℝ) - b|) = (D r a b : ℝ) := by
    intro a b ha hb hab
    rw [D_eq r a b ha hb hab]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    rw [abs_of_nonpos (by linarith), hRr]
    split_ifs with h
    · have : ((b - a : ℕ) : ℝ) = b - a := by push_cast [Nat.cast_sub hab]; ring
      have h' : ((b - a : ℕ) : ℝ) ≤ r := by exact_mod_cast h
      rw [this] at h'
      rw [Nat.cast_sub hab]; rw [min_eq_left (by linarith)]; ring
    · have h' : r < b - a := by omega
      have h'' : (r : ℝ) < b - a := by
        have : ((r : ℕ) : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast h'
        rwa [Nat.cast_sub hab] at this
      rw [Nat.cast_sub (by omega), Nat.cast_sub hab, Nat.cast_mul]
      rw [min_eq_right (by linarith)]; push_cast; ring
  rcases le_total s.val t.val with h | h
  · have := key _ _ hs ht h
    exact_mod_cast this
  · have := key _ _ ht hs h
    rw [D_comm]
    rw [abs_sub_comm] 
    exact_mod_cast this

theorem fd_cyc {R : ℕ+} (r : ℕ) (hR : (R : ℕ) = 2 * r) (hr : 1 ≤ r) :
    finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ) = r := by
  have hRr : ((R : ℕ) : ℝ) = 2 * r := by exact_mod_cast hR
  apply le_antisymm
  · unfold finiteDiameter
    refine csSup_le ⟨_, ⟨(0, 0), rfl⟩⟩ ?_
    rintro _ ⟨⟨x, y⟩, rfl⟩
    show cyclicDistance x y ≤ r
    unfold cyclicDistance
    calc _ ≤ ((|(x.val : ℝ) - y.val|) + (((R : ℕ) : ℝ) - |(x.val : ℝ) - y.val|)) / 2 := by have := min_le_left (|(x.val : ℝ) - y.val|) (((R : ℕ) : ℝ) - |(x.val : ℝ) - y.val|); have := min_le_right (|(x.val : ℝ) - y.val|) (((R : ℕ) : ℝ) - |(x.val : ℝ) - y.val|); linarith
      _ = r := by rw [hRr]; ring
  · have : NeZero (R : ℕ) := inferInstance
    have h1 : ((r : ZMod (R : ℕ))).val = r := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; omega
    have := le_finiteDiameter (cyclicDistance : ZMod (R : ℕ) → ZMod (R : ℕ) → ℝ) 0 (r : ZMod (R : ℕ))
    have e : cyclicDistance (R := R) 0 (r : ZMod (R : ℕ)) = r := by
      unfold cyclicDistance
      rw [h1, ZMod.val_zero]
      simp only [Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast, hRr]
      rw [min_eq_left (by linarith)]
    rwa [e] at this

end RamseyDisambig.Dev.Thm2
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Thm2

open RamseyDisambig.Spherical

def eqv (a n r : ℕ) : Fin a × (Fin n × Fin r) ≃ Fin (a * (n * r)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def psi {R : ℕ+} (r a b n : ℕ) (x : Torus R n) : Cube (a * (n * r) + b) :=
  Fin.append (fun ℓ => (fun p : Fin a × (Fin n × Fin r) => ph r (x p.2.1).val p.2.2) ((eqv a n r).symm ℓ))
    (fun _ : Fin b => false)

theorem ham_psi {R : ℕ+} (r a b n : ℕ) (x y : Torus R n) :
    hammingDist (psi r a b n x) (psi r a b n y) = a * ∑ j, D r (x j).val (y j).val := by
  unfold hammingDist
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [psi, Fin.append_left, Fin.append_right, ne_eq, not_true_eq_false, if_false,
    Finset.sum_const_zero, add_zero]
  rw [Equiv.sum_comp (eqv a n r).symm (fun p : Fin a × (Fin n × Fin r) =>
    if ph r (x p.2.1).val p.2.2 ≠ ph r (y p.2.1).val p.2.2 then 1 else 0)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have h : ∀ j : Fin n, (∑ i : Fin r, if ph r (x j).val i ≠ ph r (y j).val i then 1 else 0) =
      D r (x j).val (y j).val := fun j => by
    unfold D; rw [Finset.card_filter]
  calc _ = ∑ _α : Fin a, ∑ j, D r (x j).val (y j).val :=
        Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => h j
    _ = _ := by simp

theorem cubeDist_psi {R : ℕ+} (r : ℕ) (hR : (R : ℕ) = 2 * r) (a b n : ℕ) (x y : Torus R n) :
    cubeDistance (psi r a b n x) (psi r a b n y) = a * torusDistance x y + 0 := by
  unfold cubeDistance torusDistance
  rw [ham_psi]
  simp only [distanceProfile, cd_eq_D r hR, add_zero]
  push_cast
  rfl

end RamseyDisambig.Dev.Thm2
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Thm2

open RamseyDisambig.Spherical RamseyDisambig.Dev.Pullback

theorem fd_cube (N : ℕ) (hN : 1 ≤ N) :
    finiteDiameter (cubeDistance : Cube N → Cube N → ℝ) = N := by
  apply le_antisymm
  · unfold finiteDiameter
    refine csSup_le ⟨_, ⟨(0, 0), rfl⟩⟩ ?_
    rintro _ ⟨⟨x, y⟩, rfl⟩
    show cubeDistance x y ≤ N
    unfold cubeDistance
    exact_mod_cast (hammingDist_le_card_fintype (x := x) (y := y)).trans (by simp)
  · have := le_finiteDiameter (cubeDistance : Cube N → Cube N → ℝ) (fun _ => false) (fun _ => true)
    have e : cubeDistance (fun _ : Fin N => false) (fun _ => true) = N := by
      unfold cubeDistance hammingDist; simp
    rwa [e] at this

theorem gap_of_disamb (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (N : ℕ) (hN : 1 ≤ N)
    (c : Cube N → Cube N → Bool) (hc : IsGapHammingDisambiguation ε N c) :
    GapColoring ε cubeDistance c := by
  rw [GapColoring, fd_cube N hN]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · intro x y h
    apply hc x y false
    simp [gapHammingMatrix, h]
  · intro x y h
    apply hc x y true
    have : ¬ cubeDistance x y ≤ ε * N := by nlinarith
    simp [gapHammingMatrix, this, h]

end RamseyDisambig.Dev.Thm2

namespace RamseyDisambig.Spherical

open RamseyDisambig.Dev.Thm2 RamseyDisambig.Dev.Pullback

theorem chk_theorem_2 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (k : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ c : Cube N → Cube N → Bool, IsGapHammingDisambiguation ε N c →
        (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, le_rfl, fun N _ c _ => by simp⟩
  obtain ⟨N', R, hN'1, hR2, hRev, h13⟩ :=
    theorem_13 (ε / 2) (by linarith) (by linarith) k hk
  obtain ⟨r, hr⟩ := hRev
  have hR : (R : ℕ) = 2 * r := by omega
  have hr1 : 1 ≤ r := by omega
  refine ⟨max 1 ⌈2 * r * N' / ε⌉₊, le_max_left _ _, fun N hN c hc => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNc : (2 * r * N' / ε : ℝ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hrN : 0 < r * N' := by positivity
  set a := N / (r * N') with ha
  set b := N % (r * N') with hb
  have hNab : N = a * (N' * r) + b := by
    have := Nat.div_add_mod N (r * N')
    rw [mul_comm N' r, ha, hb, mul_comm (N / (r * N')) (r * N')]; exact this.symm
  have hblt : b < r * N' := Nat.mod_lt _ hrN
  have hbR : (b : ℝ) < (r * N' : ℕ) := by exact_mod_cast hblt
  have hbε : (b : ℝ) ≤ ε / 2 * N := by
    have : (2 * r * N' : ℝ) ≤ ε * N := by
      rw [div_le_iff₀ hε] at hNc; linarith
    push_cast at hbR; nlinarith
  clear_value a b
  subst hNab
  have hgap := gap_of_disamb ε hε hεhalf _ hN1 c hc
  have hdiam : (1 - ε / 2) * finiteDiameter (cubeDistance : Cube (a * (N' * r) + b) → _ → ℝ) ≤
      a * finiteDiameter (torusDistance : Torus R N' → Torus R N' → ℝ) := by
    rw [fd_cube _ hN1, RamseyDisambig.Dev.L12.diam_torus, fd_cyc r hR hr1]
    push_cast at hbε ⊢
    nlinarith
  have hpb := pullback_gap ε hε hεhalf (cubeDistance : Cube (a * (N' * r) + b) → _ → ℝ)
    (torusDistance : Torus R N' → Torus R N' → ℝ)
    (fun x y => RamseyDisambig.Dev.L12.torusDistance_nonneg x y)
    (psi r a b N') (psi r a b N') a 0 (by positivity) le_rfl
    (cubeDist_psi r hR a b N') c hgap hdiam
  have h1 := h13 _ hpb
  exact RamseyDisambig.Dev.L10.vcDim_pullback (psi r a b N') (psi r a b N') c k hk h1

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_theorem_2 := @RamseyDisambig.Spherical.chk_theorem_2
