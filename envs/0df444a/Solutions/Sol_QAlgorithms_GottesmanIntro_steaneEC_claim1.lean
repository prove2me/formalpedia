-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.steaneEC_claim1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:43:10.33717+00:00
-- url     : https://prove2.me/submissions/883bb77e-7faf-4dc6-ac7b-354243bfd090

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_GottesmanIntro_Ch04_Model
set_option autoImplicit false

open scoped Matrix BigOperators
open QAlgorithms QAlgorithms.GottesmanIntro

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

private def zmodOfBits {n : ℕ} (y : Qubits n) : Fin n → ZMod 2 :=
  fun q => if y q then 1 else 0

private lemma bitsOfZMod_zmodOfBits {n : ℕ} (y : Qubits n) :
    bitsOfZMod (zmodOfBits y) = y := by
  funext q
  cases h : y q <;> simp [bitsOfZMod, zmodOfBits, h]

private lemma zmodOfBits_bitsOfZMod {n : ℕ} (v : Fin n → ZMod 2) :
    zmodOfBits (bitsOfZMod v) = v := by
  funext q
  rcases zmod2_cases (v q) with h | h <;> simp [zmodOfBits, bitsOfZMod, h]

private lemma bitsOfZMod_injective {n : ℕ} : Function.Injective (bitsOfZMod (n := n)) := by
  intro u v h
  rw [← zmodOfBits_bitsOfZMod u, ← zmodOfBits_bitsOfZMod v, h]

private lemma bitsOfZMod_eq_iff {n : ℕ} (u v : Fin n → ZMod 2) :
    bitsOfZMod u = bitsOfZMod v ↔ u = v :=
  bitsOfZMod_injective.eq_iff

private lemma zmod2_add_self {n : ℕ} (a : Fin n → ZMod 2) :
    a + a = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (a i)

private lemma zmod2_add_cancel_left {n : ℕ} (a b : Fin n → ZMod 2) :
    a + (a + b) = b := by
  rw [← add_assoc, zmod2_add_self, zero_add]

private lemma zmod2_add_cancel_right {n : ℕ} (a b : Fin n → ZMod 2) :
    (a + b) + b = a := by
  rw [add_assoc, zmod2_add_self, add_zero]

private lemma zmod2_eq_add_iff {n : ℕ} (a b c : Fin n → ZMod 2) :
    a = b + c ↔ c = a + b := by
  constructor <;> rintro rfl
  · rw [add_comm b c, zmod2_add_cancel_right]
  · rw [add_comm a b, zmod2_add_cancel_left]

private lemma zmod2_eq_iff_add_eq_zero {n : ℕ} (a b : Fin n → ZMod 2) :
    a = b ↔ a + b = 0 := by
  constructor
  · rintro rfl; exact zmod2_add_self a
  · intro h
    rw [← add_zero a, ← zmod2_add_self b, ← add_assoc, h, zero_add]

private def chi (s : ZMod 2) : ℂ :=
  if s = 1 then -1 else 1

private lemma chi_zero : chi 0 = 1 := rfl
private lemma chi_one : chi 1 = -1 := rfl

private lemma chi_add (s t : ZMod 2) : chi (s + t) = chi s * chi t := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;>
    simp [chi]

private lemma chi_mul_self (s : ZMod 2) : chi s * chi s = 1 := by
  rw [← chi_add, CharTwo.add_self_eq_zero, chi_zero]

private lemma prod_chi {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∏ i, chi (f i)) = chi (∑ i, f i) := by
  classical
  induction' (Finset.univ : Finset ι) using Finset.cons_induction with a s ha ih
  · simp [chi_zero]
  · rw [Finset.prod_cons, Finset.sum_cons, chi_add, ih]

private lemma prod_chi_dotProduct {n : ℕ} (u v : Fin n → ZMod 2) :
    (∏ q : Fin n, chi (u q * v q)) = chi (u ⬝ᵥ v) := by
  rw [prod_chi, dotProduct]

private lemma sum_chi_single (u : ZMod 2) :
    (∑ b : ZMod 2, chi (u * b)) = if u = 0 then 2 else 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]
  rcases zmod2_cases u with rfl | rfl <;> (simp [chi]; try norm_num)

private lemma sum_chi_dotProduct {k : ℕ} (u : Fin k → ZMod 2) :
    (∑ b : Fin k → ZMod 2, chi (u ⬝ᵥ b)) = if u = 0 then (2 : ℂ) ^ k else 0 := by
  simp_rw [← prod_chi_dotProduct]
  rw [← Fintype.prod_sum (fun i b => chi (u i * b))]
  simp_rw [sum_chi_single]
  by_cases hu : u = 0
  · subst hu
    simp
  · rw [if_neg hu]
    have hex : ∃ i : Fin k, u i ≠ 0 := by
      by_contra h
      exact hu (funext fun i => not_not.mp (forall_not_of_not_exists h i))
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma singlePauli_apply (a b : ZMod 2) (y z : Bool) :
    ((if b = 1 then pauliZ else 1) * (if a = 1 then pauliX else 1)) y z =
      if y = decide ((if z then (1 : ZMod 2) else 0) + a = 1) then
        chi ((if y then (1 : ZMod 2) else 0) * b)
      else 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    cases y <;> cases z <;>
    simp [pauliZ, pauliX, chi, Matrix.mul_apply]

private lemma rowPauli_apply {n : ℕ} (a b : Fin n → ZMod 2) (y z : Qubits n) :
    rowPauli a b y z =
      if y = bitsOfZMod (zmodOfBits z + a) then chi (zmodOfBits y ⬝ᵥ b) else 0 := by
  unfold rowPauli kronAll
  rw [Matrix.of_apply]
  have hfactor : ∀ q : Fin n,
      ((if b q = 1 then pauliZ else 1) * (if a q = 1 then pauliX else 1)) (y q) (z q) =
        if y q = bitsOfZMod (zmodOfBits z + a) q then chi (zmodOfBits y q * b q) else 0 :=
    fun q => singlePauli_apply (a q) (b q) (y q) (z q)
  simp_rw [hfactor]
  by_cases hy : y = bitsOfZMod (zmodOfBits z + a)
  · rw [if_pos hy]
    have hq : ∀ q : Fin n, y q = bitsOfZMod (zmodOfBits z + a) q := congrFun hy
    have hprod : (∏ q : Fin n,
        if y q = bitsOfZMod (zmodOfBits z + a) q then chi (zmodOfBits y q * b q) else 0) =
        ∏ q : Fin n, chi (zmodOfBits y q * b q) := by
      refine Finset.prod_congr rfl fun q _ => if_pos (hq q)
    rw [hprod]
    exact prod_chi_dotProduct (zmodOfBits y) b
  · rw [if_neg hy]
    have hex : ∃ q : Fin n, y q ≠ bitsOfZMod (zmodOfBits z + a) q := by
      by_contra h
      exact hy (funext fun q => not_not.mp (forall_not_of_not_exists h q))
    rcases hex with ⟨q, hq⟩
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

private noncomputable def pauliCoeff {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (a b : Fin k → ZMod 2) : ℂ :=
  ((2 : ℂ) ^ k)⁻¹ *
    ∑ u : Qubits k, chi (zmodOfBits u ⬝ᵥ b) * M u (bitsOfZMod (zmodOfBits u + a))

private lemma matrix_eq_sum_rowPauli {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) :
    M = ∑ a : Fin k → ZMod 2, ∑ b : Fin k → ZMod 2, pauliCoeff M a b • rowPauli a b := by
  ext y z
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, rowPauli_apply]
  have ha_iff : ∀ a : Fin k → ZMod 2,
      y = bitsOfZMod (zmodOfBits z + a) ↔ a = zmodOfBits y + zmodOfBits z := by
    intro a
    rw [← bitsOfZMod_zmodOfBits y, bitsOfZMod_eq_iff, bitsOfZMod_zmodOfBits]
    exact zmod2_eq_add_iff (zmodOfBits y) (zmodOfBits z) a
  simp_rw [ha_iff, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_eq_single (zmodOfBits y + zmodOfBits z)]
  · rw [if_pos rfl]
    unfold pauliCoeff
    simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ u : Qubits k,
        (∑ b : Fin k → ZMod 2,
          chi (zmodOfBits u ⬝ᵥ b) *
            M u (bitsOfZMod (zmodOfBits u + (zmodOfBits y + zmodOfBits z))) *
              chi (zmodOfBits y ⬝ᵥ b)) =
          if u = y then (2 : ℂ) ^ k * M y z else 0 := by
      intro u
      have hterm : ∀ b : Fin k → ZMod 2,
          chi (zmodOfBits u ⬝ᵥ b) *
            M u (bitsOfZMod (zmodOfBits u + (zmodOfBits y + zmodOfBits z))) *
              chi (zmodOfBits y ⬝ᵥ b) =
            M u (bitsOfZMod (zmodOfBits u + (zmodOfBits y + zmodOfBits z))) *
              chi ((zmodOfBits u + zmodOfBits y) ⬝ᵥ b) := by
        intro b
        rw [add_dotProduct, chi_add]
        ring
      simp_rw [hterm, ← Finset.mul_sum, sum_chi_dotProduct]
      by_cases huy : u = y
      · subst huy
        have h0 : zmodOfBits u + zmodOfBits u = 0 := zmod2_add_self _
        have hz : bitsOfZMod (zmodOfBits u + (zmodOfBits u + zmodOfBits z)) = z := by
          rw [zmod2_add_cancel_left, bitsOfZMod_zmodOfBits]
        rw [if_pos rfl, if_pos h0, hz, mul_comm]
      · have hne : zmodOfBits u + zmodOfBits y ≠ 0 := by
          intro h0
          apply huy
          have h1 : zmodOfBits u = zmodOfBits y :=
            (zmod2_eq_iff_add_eq_zero _ _).mpr h0
          rw [← bitsOfZMod_zmodOfBits u, ← bitsOfZMod_zmodOfBits y, h1]
        rw [if_neg huy, if_neg hne, mul_zero]
    simp_rw [hinner, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k (by norm_num)), one_mul]
  · intro a _ ha
    exact if_neg ha
  · intro ha
    exact absurd (Finset.mem_univ _) ha

private def liftVec {k n : ℕ} (w : Fin k ↪ Fin n) (a : Fin k → ZMod 2) : Fin n → ZMod 2 :=
  fun q => ∑ i : Fin k, if w i = q then a i else 0

private lemma liftVec_apply_range {k n : ℕ} (w : Fin k ↪ Fin n) (a : Fin k → ZMod 2) (i : Fin k) :
    liftVec w a (w i) = a i := by
  simp [liftVec, w.injective.eq_iff]

private lemma liftVec_apply_not_mem {k n : ℕ} (w : Fin k ↪ Fin n) (a : Fin k → ZMod 2)
    {q : Fin n} (hq : q ∉ Set.range w) : liftVec w a q = 0 := by
  unfold liftVec
  refine Finset.sum_eq_zero fun i _ => if_neg ?_
  intro h
  exact hq ⟨i, h⟩

private lemma dotProduct_liftVec {k n : ℕ} (w : Fin k ↪ Fin n) (u : Fin n → ZMod 2)
    (b : Fin k → ZMod 2) :
    u ⬝ᵥ liftVec w b = (u ∘ w) ⬝ᵥ b := by
  unfold dotProduct liftVec
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Function.comp_apply]

private lemma embedOp_rowPauli {k n : ℕ} (w : Fin k ↪ Fin n) (a b : Fin k → ZMod 2) :
    embedOp (rowPauli a b) w = rowPauli (liftVec w a) (liftVec w b) := by
  ext y z
  rw [embedOp, Matrix.of_apply, rowPauli_apply, rowPauli_apply]
  by_cases hy : y = bitsOfZMod (zmodOfBits z + liftVec w a)
  · have hoff : ∀ q : Fin n, q ∉ Set.range w → y q = z q := by
      intro q hq
      rw [hy, bitsOfZMod, Pi.add_apply, liftVec_apply_not_mem w a hq, add_zero]
      exact congrFun (bitsOfZMod_zmodOfBits z) q
    have hon : y ∘ w = bitsOfZMod (zmodOfBits (z ∘ w) + a) := by
      funext i
      rw [Function.comp_apply, hy, bitsOfZMod, bitsOfZMod, Pi.add_apply, Pi.add_apply,
        liftVec_apply_range]
      rfl
    rw [if_pos hoff, if_pos hon, if_pos hy]
    congr 1
    exact (dotProduct_liftVec w (zmodOfBits y) b).symm
  · rw [if_neg hy]
    by_cases hoff : ∀ q : Fin n, q ∉ Set.range w → y q = z q
    · rw [if_pos hoff, if_neg]
      intro hon
      apply hy
      funext q
      by_cases hq : q ∈ Set.range w
      · rcases hq with ⟨i, rfl⟩
        have hi := congrFun hon i
        change y (w i) = bitsOfZMod (zmodOfBits (z ∘ w) + a) i at hi
        rw [hi, bitsOfZMod, bitsOfZMod, Pi.add_apply, Pi.add_apply, liftVec_apply_range]
        rfl
      · rw [hoff q hq, bitsOfZMod, Pi.add_apply, liftVec_apply_not_mem w a hq, add_zero]
        exact (congrFun (bitsOfZMod_zmodOfBits z) q).symm
    · rw [if_neg hoff]

private def SuppIn {n : ℕ} (F : Finset (Fin n)) (a : Fin n → ZMod 2) : Prop :=
  ∀ q ∉ F, a q = 0

private lemma suppIn_zero {n : ℕ} (F : Finset (Fin n)) : SuppIn F 0 :=
  fun _ _ => rfl

private lemma suppIn_add {n : ℕ} {F : Finset (Fin n)} {a b : Fin n → ZMod 2}
    (ha : SuppIn F a) (hb : SuppIn F b) : SuppIn F (a + b) := by
  intro q hq
  rw [Pi.add_apply, ha q hq, hb q hq, add_zero]

private lemma suppIn_mono {n : ℕ} {F1 F2 : Finset (Fin n)} (hF : F1 ⊆ F2)
    {a : Fin n → ZMod 2} (ha : SuppIn F1 a) : SuppIn F2 a :=
  fun q hq => ha q (fun h => hq (hF h))

private lemma suppIn_liftVec {k n : ℕ} {F : Finset (Fin n)} {w : Fin k ↪ Fin n}
    (hw : Set.range w ⊆ (F : Set (Fin n))) (a : Fin k → ZMod 2) :
    SuppIn F (liftVec w a) := by
  intro q hq
  exact liftVec_apply_not_mem w a (fun hr => hq (hw hr))

private lemma actsWithin_rowPauli {n : ℕ} (F : Finset (Fin n)) (a b : Fin n → ZMod 2)
    (ha : SuppIn F a) (hb : SuppIn F b) : ActsWithin F (rowPauli a b) := by
  let e : Fin F.card ≃ F := F.equivFin.symm
  let w : Fin F.card ↪ Fin n := ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩
  refine ⟨F.card, w, rowPauli (a ∘ w) (b ∘ w), ?_, ?_⟩
  · rintro q ⟨i, rfl⟩
    exact (e i).2
  · rw [embedOp_rowPauli]
    have hrec : ∀ c : Fin n → ZMod 2, SuppIn F c → liftVec w (c ∘ w) = c := by
      intro c hc
      funext q
      by_cases hq : q ∈ F
      · have hq' : w (e.symm ⟨q, hq⟩) = q := by
          change (e (e.symm ⟨q, hq⟩)).1 = q
          rw [Equiv.apply_symm_apply]
        rw [← hq', liftVec_apply_range, Function.comp_apply]
      · have hq_range : q ∉ Set.range w := by
          rintro ⟨i, rfl⟩
          exact hq (e i).2
        rw [liftVec_apply_not_mem w (c ∘ w) hq_range, hc q hq]
    rw [hrec a ha, hrec b hb]

private lemma mem_of_forall_mem_binDual {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : ∀ h ∈ binDual C, h ⬝ᵥ v = 0) : v ∈ C := by
  by_contra hnot
  have hu : C.mkQ v ≠ 0 := by
    intro h
    exact hnot ((Submodule.Quotient.mk_eq_zero C).mp h)
  let B := Module.Basis.ofVectorSpace (ZMod 2) ((Fin n → ZMod 2) ⧸ C)
  have hrepr : B.repr (C.mkQ v) ≠ 0 :=
    B.repr.map_ne_zero_iff.mpr hu
  have hex : ∃ i, B.repr (C.mkQ v) i ≠ 0 := by
    by_contra h0
    apply hrepr
    ext i
    exact not_not.mp (forall_not_of_not_exists h0 i)
  rcases hex with ⟨i0, hi0⟩
  let g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply i0).comp (B.repr.toLinearMap.comp C.mkQ)
  let h : Fin n → ZMod 2 := fun j => g (Pi.single j 1)
  have hg_eq : ∀ x : Fin n → ZMod 2, g x = x ⬝ᵥ h := by
    intro x
    have hx_sum : x = ∑ j : Fin n, x j • Pi.single j 1 := by
      ext j; simp [Pi.single_apply]
    conv_lhs => rw [hx_sum]
    rw [map_sum]
    simp only [h, dotProduct, map_smul, smul_eq_mul]
  have hh : h ∈ binDual C := by
    intro c hc
    rw [← hg_eq c]
    have hc0 : C.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero C).mpr hc
    simp [g, hc0]
  have hgv : g v = 0 := by
    rw [hg_eq v, dotProduct_comm]
    exact hv h hh
  exact hi0 hgv

private lemma act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u v : EuclideanSpace ℂ ι) : act A (u + v) = act A u + act A v := by
  ext i; simp [act, Matrix.mulVec_add]

private lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (u : EuclideanSpace ℂ ι) : act A (c • u) = c • act A u := by
  ext i; simp [act, Matrix.mulVec_smul]

private lemma act_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    act A (0 : EuclideanSpace ℂ ι) = 0 := by
  ext i; simp [act]

private lemma add_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (u : EuclideanSpace ℂ ι) : act (A + B) u = act A u + act B u := by
  ext i; simp [act, Matrix.add_mulVec]

private lemma smul_act {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ)
    (u : EuclideanSpace ℂ ι) : act (c • A) u = c • act A u := by
  ext i; simp [act, Matrix.smul_mulVec]

private lemma zero_act {ι : Type*} [Fintype ι] (u : EuclideanSpace ℂ ι) :
    act (0 : Matrix ι ι ℂ) u = 0 := by
  ext i; simp [act]

private lemma act_sum {α ι : Type*} [Fintype ι] (s : Finset α) (A : Matrix ι ι ℂ)
    (f : α → EuclideanSpace ℂ ι) :
    act A (∑ x ∈ s, f x) = ∑ x ∈ s, act A (f x) := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · simp [act_zero]
  · rw [Finset.sum_cons, act_add, ih, Finset.sum_cons]

private lemma tensorVec_add_left {ι κ : Type*} (u1 u2 : EuclideanSpace ℂ ι)
    (v : EuclideanSpace ℂ κ) :
    tensorVec (u1 + u2) v = tensorVec u1 v + tensorVec u2 v := by
  ext p; simp [tensorVec, add_mul]

private lemma tensorVec_smul_left {ι κ : Type*} (c : ℂ) (u : EuclideanSpace ℂ ι)
    (v : EuclideanSpace ℂ κ) :
    tensorVec (c • u) v = c • tensorVec u v := by
  ext p; simp [tensorVec, mul_assoc]

private lemma tensorVec_zero_left {ι κ : Type*} (v : EuclideanSpace ℂ κ) :
    tensorVec (0 : EuclideanSpace ℂ ι) v = 0 := by
  ext p; simp [tensorVec]

private lemma tensorVec_add_right {ι κ : Type*} (u : EuclideanSpace ℂ ι)
    (v1 v2 : EuclideanSpace ℂ κ) :
    tensorVec u (v1 + v2) = tensorVec u v1 + tensorVec u v2 := by
  ext p; simp [tensorVec, mul_add]

private lemma tensorVec_smul_right {ι κ : Type*} (c : ℂ) (u : EuclideanSpace ℂ ι)
    (v : EuclideanSpace ℂ κ) :
    tensorVec u (c • v) = c • tensorVec u v := by
  ext p; simp [tensorVec, mul_left_comm]

private lemma tensorVec_zero_right {ι κ : Type*} (u : EuclideanSpace ℂ ι) :
    tensorVec u (0 : EuclideanSpace ℂ κ) = 0 := by
  ext p; simp [tensorVec]

private lemma tensorVec_sum_left {α ι κ : Type*} (s : Finset α) (f : α → EuclideanSpace ℂ ι)
    (v : EuclideanSpace ℂ κ) :
    tensorVec (∑ x ∈ s, f x) v = ∑ x ∈ s, tensorVec (f x) v := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · simp [tensorVec_zero_left]
  · rw [Finset.sum_cons, tensorVec_add_left, ih, Finset.sum_cons]

private lemma tensorVec_sum_right {α ι κ : Type*} (s : Finset α) (u : EuclideanSpace ℂ ι)
    (f : α → EuclideanSpace ℂ κ) :
    tensorVec u (∑ x ∈ s, f x) = ∑ x ∈ s, tensorVec u (f x) := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · simp [tensorVec_zero_right]
  · rw [Finset.sum_cons, tensorVec_add_right, ih, Finset.sum_cons]

private lemma mem_submodule_of_linear_sum {α E : Type*} [AddCommMonoid α]
    [AddCommMonoid E] [Module ℂ E] (V : Submodule ℂ E) (f : α → E)
    (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    {ι : Type*} (s : Finset ι) (x : ι → α)
    (hx : ∀ i ∈ s, f (x i) ∈ V) :
    f (∑ i ∈ s, x i) ∈ V := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · rw [Finset.sum_empty, h0]; exact V.zero_mem
  · rw [Finset.sum_cons, hadd]
    exact V.add_mem (hx a (Finset.mem_cons_self a t))
      (ih fun i hi => hx i (Finset.mem_cons_of_mem hi))

private lemma mem_submodule_of_linear {α E : Type*} [AddCommMonoid α] [Module ℂ α]
    [AddCommMonoid E] [Module ℂ E] (V : Submodule ℂ E) (f : α → E)
    (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℂ) x, f (c • x) = c • f x)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → α)
    (hx : ∀ i ∈ s, f (x i) ∈ V) :
    f (∑ i ∈ s, c i • x i) ∈ V := by
  refine mem_submodule_of_linear_sum V f h0 hadd s (fun i => c i • x i) fun i hi => ?_
  rw [hsmul]
  exact V.smul_mem (c i) (hx i hi)

private lemma embedOp_zero {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (0 : Matrix (Qubits k) (Qubits k) ℂ) w = 0 := by
  ext y z; simp [embedOp]

private lemma embedOp_add {k n : ℕ} (M1 M2 : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp (M1 + M2) w = embedOp M1 w + embedOp M2 w := by
  ext y z; simp [embedOp, ite_add_zero]

private lemma embedOp_smul {k n : ℕ} (c : ℂ) (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp (c • M) w = c • embedOp M w := by
  ext y z; simp [embedOp, mul_ite]

private lemma actsWithin_span {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (V : Submodule ℂ E) (F F' : Finset (Fin n)) (hF : F' ⊆ F)
    (f : Matrix (Qubits n) (Qubits n) ℂ → E)
    (h0 : f 0 = 0) (hadd : ∀ X Y, f (X + Y) = f X + f Y)
    (hsmul : ∀ (c : ℂ) X, f (c • X) = c • f X)
    (hpauli : ∀ a b : Fin n → ZMod 2, SuppIn F a → SuppIn F b → f (rowPauli a b) ∈ V)
    {M : Matrix (Qubits n) (Qubits n) ℂ} (hM : ActsWithin F' M) :
    f M ∈ V := by
  rcases hM with ⟨k, w, Mk, hw, rfl⟩
  rw [matrix_eq_sum_rowPauli Mk]
  have hwF : Set.range w ⊆ (F : Set (Fin n)) := Set.Subset.trans hw hF
  refine mem_submodule_of_linear_sum V (fun X => f (embedOp X w))
    (by rw [embedOp_zero, h0])
    (fun X Y => by rw [embedOp_add, hadd])
    Finset.univ
    (fun a => ∑ b : Fin k → ZMod 2, pauliCoeff Mk a b • rowPauli a b) ?_
  intro a _
  refine mem_submodule_of_linear V (fun X => f (embedOp X w))
    (by rw [embedOp_zero, h0])
    (fun X Y => by rw [embedOp_add, hadd])
    (fun c X => by rw [embedOp_smul, hsmul])
    Finset.univ (fun b => pauliCoeff Mk a b)
    (fun b => rowPauli a b) ?_
  intro b _
  rw [embedOp_rowPauli]
  exact hpauli (liftVec w a) (liftVec w b) (suppIn_liftVec hwF a) (suppIn_liftVec hwF b)

private lemma rowPauli_submatrix_qubitsAppend {n : ℕ} (A B : Fin (n + n) → ZMod 2) :
    (rowPauli A B).submatrix (qubitsAppendEquiv n n).symm (qubitsAppendEquiv n n).symm =
      Matrix.kronecker
        (rowPauli (fun i => A (Fin.castAdd n i)) (fun i => B (Fin.castAdd n i)))
        (rowPauli (fun i => A (Fin.natAdd n i)) (fun i => B (Fin.natAdd n i))) := by
  ext ⟨y1, y2⟩ ⟨z1, z2⟩
  simp only [Matrix.submatrix_apply, qubitsAppendEquiv, Equiv.coe_fn_symm_mk,
    Matrix.kronecker, Matrix.kroneckerMap_apply, rowPauli, kronAll, Matrix.of_apply]
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Fin.append_left]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.append_right]

private lemma actsWithinPair_span {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (V : Submodule ℂ E) (F g : Finset (Fin n)) (hg : g ⊆ F)
    (f : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ → E)
    (h0 : f 0 = 0) (hadd : ∀ X Y, f (X + Y) = f X + f Y)
    (hsmul : ∀ (c : ℂ) X, f (c • X) = c • f X)
    (hpauli : ∀ a1 b1 a2 b2 : Fin n → ZMod 2,
      SuppIn F a1 → SuppIn F b1 → SuppIn F a2 → SuppIn F b2 →
        f (Matrix.kronecker (rowPauli a1 b1) (rowPauli a2 b2)) ∈ V)
    {G : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ} (hG : ActsWithinPair g G) :
    f G ∈ V := by
  rcases hG with ⟨G', hG', rfl⟩
  let g2 : Finset (Fin (n + n)) := g.image (Fin.castAdd n) ∪ g.image (Fin.natAdd n)
  refine actsWithin_span V g2 g2 Finset.Subset.rfl
    (fun X => f (X.submatrix (qubitsAppendEquiv n n).symm (qubitsAppendEquiv n n).symm))
    (by simp [h0])
    (fun X Y => by simp [Matrix.submatrix_add, hadd])
    (fun c X => by simp [Matrix.submatrix_smul, hsmul])
    ?_ hG'
  intro A B hA hB
  rw [rowPauli_submatrix_qubitsAppend]
  have hcast : ∀ C : Fin (n + n) → ZMod 2, SuppIn g2 C → SuppIn F (fun i => C (Fin.castAdd n i)) := by
    intro C hC q hq
    apply hC (Fin.castAdd n q)
    simp only [g2, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨fun i hi h => hq (hg ((Fin.castAdd_injective n n h) ▸ hi)), fun i _ h => ?_⟩
    exact absurd h (castAdd_ne_natAdd q i)
  have hnat : ∀ C : Fin (n + n) → ZMod 2, SuppIn g2 C → SuppIn F (fun i => C (Fin.natAdd n i)) := by
    intro C hC q hq
    apply hC (Fin.natAdd n q)
    simp only [g2, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨fun i _ h => absurd h.symm (castAdd_ne_natAdd i q), fun i hi h => ?_⟩
    exact hq (hg ((Fin.natAdd_injective n n h) ▸ hi))
  exact hpauli _ _ _ _ (hcast A hA) (hcast B hB) (hnat A hA) (hnat B hB)

private lemma ket_apply {ι : Type*} [DecidableEq ι] (i j : ι) :
    ket i j = if j = i then (1 : ℂ) else 0 := by
  simp [ket, eq_comm]

private lemma act_ket_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    act A (ket i) j = A j i := by
  simp [act, ket]

private lemma act_ket_eq_smul_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (c : ℂ)
    (hA : ∀ k : ι, A k i = if k = j then c else 0) :
    act A (ket i) = c • ket j := by
  ext k
  rw [act_ket_apply, hA k, PiLp.smul_apply, ket_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

private lemma act_rowPauli_ket {n : ℕ} (a b v : Fin n → ZMod 2) :
    act (rowPauli a b) (ket (bitsOfZMod v)) =
      chi ((v + a) ⬝ᵥ b) • ket (bitsOfZMod (v + a)) := by
  refine act_ket_eq_smul_ket _ _ _ _ fun k => ?_
  rw [rowPauli_apply, zmodOfBits_bitsOfZMod]
  by_cases hk : k = bitsOfZMod (v + a)
  · rw [if_pos hk, if_pos hk, hk, zmodOfBits_bitsOfZMod]
  · rw [if_neg hk, if_neg hk]

private lemma tensorVec_ket {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    tensorVec (ket i) (ket j) = ket (i, j) := by
  ext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;>
    simp [tensorVec, ket, hi, hj]

private lemma cnot_bitsOfZMod {n : ℕ} (d b : Fin n → ZMod 2) (z1 z2 : Qubits n) (i : Fin n) :
    cnot (z1 i, z2 i) (bitsOfZMod d i, bitsOfZMod b i) =
      if z1 i = bitsOfZMod d i ∧ z2 i = bitsOfZMod (b + d) i then 1 else 0 := by
  simp only [cnot, Matrix.of_apply, bitsOfZMod, Pi.add_apply]
  rcases zmod2_cases (d i) with hd | hd <;> rcases zmod2_cases (b i) with hb | hb <;>
    cases z1 i <;> cases z2 i <;> simp [hd, hb]

private lemma transCnot_apply_bitsOfZMod {n : ℕ} (d b : Fin n → ZMod 2) (z1 z2 : Qubits n) :
    transCnot n (z1, z2) (bitsOfZMod d, bitsOfZMod b) =
      if (z1, z2) = (bitsOfZMod d, bitsOfZMod (b + d)) then 1 else 0 := by
  unfold transCnot
  rw [Matrix.of_apply]
  simp_rw [cnot_bitsOfZMod]
  by_cases h : (z1, z2) = (bitsOfZMod d, bitsOfZMod (b + d))
  · rw [if_pos h]
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    simp
  · rw [if_neg h]
    have hex : ∃ i : Fin n, ¬ (z1 i = bitsOfZMod d i ∧ z2 i = bitsOfZMod (b + d) i) := by
      by_contra hall
      push Not at hall
      exact h (Prod.ext (funext fun i => (hall i).1) (funext fun i => (hall i).2))
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma mul_transCnot_swap_bitsOfZMod {n : ℕ}
    (GP : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (d p : Fin n → ZMod 2) (y1 y2 : Qubits n) :
    (GP * (transCnot n).submatrix Prod.swap Prod.swap) (y1, y2) (bitsOfZMod d, bitsOfZMod p) =
      GP (y1, y2) (bitsOfZMod (d + p), bitsOfZMod p) := by
  rw [Matrix.mul_apply]
  have hsub : ∀ z : Qubits n × Qubits n,
      (transCnot n).submatrix Prod.swap Prod.swap z (bitsOfZMod d, bitsOfZMod p) =
        if z = (bitsOfZMod (d + p), bitsOfZMod p) then 1 else 0 := by
    rintro ⟨z1, z2⟩
    simp only [Matrix.submatrix_apply, Prod.swap_prod_mk, transCnot_apply_bitsOfZMod,
      Prod.mk.injEq, and_comm]
  simp_rw [hsub, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma mul_transCnot_bitsOfZMod {n : ℕ}
    (GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (d b : Fin n → ZMod 2) (y1 y2 : Qubits n) :
    (GB * transCnot n) (y1, y2) (bitsOfZMod d, bitsOfZMod b) =
      GB (y1, y2) (bitsOfZMod d, bitsOfZMod (b + d)) := by
  rw [Matrix.mul_apply]
  have hsub : ∀ z : Qubits n × Qubits n,
      transCnot n z (bitsOfZMod d, bitsOfZMod b) =
        if z = (bitsOfZMod d, bitsOfZMod (b + d)) then 1 else 0 := by
    rintro ⟨z1, z2⟩
    exact transCnot_apply_bitsOfZMod d b z1 z2
  simp_rw [hsub, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma kronecker_rowPauli_bitsOfZMod {n : ℕ} (a1 b1 a2 b2 u1 u2 : Fin n → ZMod 2)
    (y1 y2 : Qubits n) :
    Matrix.kronecker (rowPauli a1 b1) (rowPauli a2 b2) (y1, y2)
        (bitsOfZMod u1, bitsOfZMod u2) =
      if (y1, y2) = (bitsOfZMod (u1 + a1), bitsOfZMod (u2 + a2)) then
        chi ((u1 + a1) ⬝ᵥ b1) * chi ((u2 + a2) ⬝ᵥ b2)
      else 0 := by
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, rowPauli_apply, zmodOfBits_bitsOfZMod]
  by_cases h1 : y1 = bitsOfZMod (u1 + a1)
  · by_cases h2 : y2 = bitsOfZMod (u2 + a2)
    · subst h1; subst h2
      simp [zmodOfBits_bitsOfZMod]
    · simp [h1, h2]
  · simp [h1]

private lemma act_liftDataPhase_ket {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (d' p' b' d1 p1 : Qubits n) (r' : R) (c : ℂ)
    (hM : ∀ y1 y2, M (y1, y2) (d', p') = if (y1, y2) = (d1, p1) then c else 0) :
    act (liftDataPhase (R := R) M) (ket ((d', r'), (p', b'))) =
      c • ket ((d1, r'), (p1, b')) := by
  refine act_ket_eq_smul_ket _ _ _ _ fun ⟨⟨y1, r1⟩, ⟨y2, y3⟩⟩ => ?_
  simp only [liftDataPhase, Matrix.of_apply, hM y1 y2, Prod.mk.injEq]
  by_cases h : r1 = r' ∧ y3 = b'
  · rcases h with ⟨rfl, rfl⟩; simp
  · rw [if_neg h, if_neg]
    rintro ⟨⟨_, hr⟩, ⟨_, hb⟩⟩
    exact h ⟨hr, hb⟩

private lemma act_liftDataBit_ket {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (d' p' b' d1 b1 : Qubits n) (r' : R) (c : ℂ)
    (hM : ∀ y1 y3, M (y1, y3) (d', b') = if (y1, y3) = (d1, b1) then c else 0) :
    act (liftDataBit (R := R) M) (ket ((d', r'), (p', b'))) =
      c • ket ((d1, r'), (p', b1)) := by
  refine act_ket_eq_smul_ket _ _ _ _ fun ⟨⟨y1, r1⟩, ⟨y2, y3⟩⟩ => ?_
  simp only [liftDataBit, Matrix.of_apply, hM y1 y3, Prod.mk.injEq]
  by_cases h : r1 = r' ∧ y2 = p'
  · rcases h with ⟨rfl, rfl⟩; simp
  · rw [if_neg h, if_neg]
    rintro ⟨⟨_, hr⟩, ⟨hp, _⟩⟩
    exact h ⟨hr, hp⟩

private lemma bool_add_decide_zmod2 (s t : ZMod 2) :
    (decide (s = 1) + decide (t = 1) : Bool) = decide (s + t = 1) := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;> decide

private lemma bool_and_decide_zmod2 (s t : ZMod 2) :
    (decide (s = 1) && decide (t = 1)) = decide (s * t = 1) := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;> decide

private lemma sum_decide_zmod2 {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∑ i : ι, decide (f i = 1) : Bool) = decide ((∑ i : ι, f i) = 1) := by
  classical
  induction' (Finset.univ : Finset ι) using Finset.cons_induction with a s ha ih
  · rw [Finset.sum_empty, Finset.sum_empty]; rfl
  · rw [Finset.sum_cons, Finset.sum_cons, ih, bool_add_decide_zmod2]

private lemma dotBits_bitsOfZMod {n : ℕ} (p m : Fin n → ZMod 2) :
    dotBits (bitsOfZMod p) (bitsOfZMod m) = decide (p ⬝ᵥ m = 1) := by
  unfold dotBits bitsOfZMod dotProduct
  simp_rw [bool_and_decide_zmod2]
  exact sum_decide_zmod2 fun k => p k * m k

private lemma hadamardN_bitsOfZMod {n : ℕ} (m p : Fin n → ZMod 2) :
    hadamardN n (bitsOfZMod m) (bitsOfZMod p) =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (p ⬝ᵥ m) := by
  unfold hadamardN chi
  rw [Matrix.of_apply, dotBits_bitsOfZMod]
  by_cases h : p ⬝ᵥ m = 1 <;> simp [h]

private lemma rowPauli_mul_hadamardN_bitsOfZMod {n : ℕ} (aHP bHP wP p : Fin n → ZMod 2) :
    (rowPauli aHP bHP * hadamardN n) (bitsOfZMod wP) (bitsOfZMod p) =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) * chi (p ⬝ᵥ (wP + aHP)) := by
  rw [Matrix.mul_apply]
  have hrow : ∀ z : Qubits n,
      rowPauli aHP bHP (bitsOfZMod wP) z =
        if z = bitsOfZMod (wP + aHP) then chi (wP ⬝ᵥ bHP) else 0 := by
    intro z
    rw [rowPauli_apply, zmodOfBits_bitsOfZMod]
    have hiff : bitsOfZMod wP = bitsOfZMod (zmodOfBits z + aHP) ↔ z = bitsOfZMod (wP + aHP) := by
      constructor
      · intro h
        have h1 := bitsOfZMod_injective h
        rw [← bitsOfZMod_zmodOfBits z, h1, zmod2_add_cancel_right]
      · rintro rfl
        rw [zmodOfBits_bitsOfZMod, zmod2_add_cancel_right]
    exact if_congr hiff rfl rfl
  simp_rw [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hadamardN_bitsOfZMod]
  ring

private noncomputable def slice3 {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    EuclideanSpace ℂ (Qubits n × R) :=
  let s3 := act (Matrix.kronecker (1 : Matrix (Qubits n × R) (Qubits n × R) ℂ)
    (Matrix.kronecker MP MB)) s2
  WithLp.toLp 2 fun p => s3 (p, (bitsOfZMod wP, bitsOfZMod wB))

private lemma slice3_add {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (u v : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP MB wP wB (u + v) = slice3 MP MB wP wB u + slice3 MP MB wP wB v := by
  ext p
  simp [slice3, act_add]

private lemma slice3_smul {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (c : ℂ) (u : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP MB wP wB (c • u) = c • slice3 MP MB wP wB u := by
  ext p
  simp [slice3, act_smul]

private lemma slice3_zero {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2) :
    slice3 MP MB wP wB (0 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) = 0 := by
  ext p
  simp [slice3, act_zero]

private lemma slice3_sum {n : ℕ} {ι : Type*} {R : Type*} [Fintype R] [DecidableEq R]
    (s : Finset ι) (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (f : ι → EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP MB wP wB (∑ x ∈ s, f x) = ∑ x ∈ s, slice3 MP MB wP wB (f x) := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · simp [slice3_zero]
  · rw [Finset.sum_cons, slice3_add, ih, Finset.sum_cons]

private lemma slice3_ket {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (d' p' b' : Qubits n) (r' : R) :
    slice3 MP MB wP wB (ket ((d', r'), (p', b'))) =
      (MP (bitsOfZMod wP) p' * MB (bitsOfZMod wB) b') • ket (d', r') := by
  ext qr
  change act (Matrix.kronecker (1 : Matrix (Qubits n × R) (Qubits n × R) ℂ)
      (Matrix.kronecker MP MB)) (ket ((d', r'), (p', b')))
      (qr, (bitsOfZMod wP, bitsOfZMod wB)) =
    ((MP (bitsOfZMod wP) p' * MB (bitsOfZMod wB) b') • ket (d', r')) qr
  rw [act_ket_apply, PiLp.smul_apply, ket_apply, smul_eq_mul]
  by_cases h : qr = (d', r')
  · subst h
    simp [Matrix.kronecker]
  · simp [Matrix.kronecker, h]

private lemma act_decoder_ket {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (dB dP d : Fin n → ZMod 2) (r : R) :
    act (Matrix.kronecker (rowPauli dB dP) (1 : Matrix R R ℂ)) (ket (bitsOfZMod d, r)) =
      chi ((d + dB) ⬝ᵥ dP) • tensorVec (ket (bitsOfZMod (d + dB))) (ket r) := by
  rw [tensorVec_ket]
  refine act_ket_eq_smul_ket _ _ _ _ fun ⟨y, r'⟩ => ?_
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, rowPauli_apply, zmodOfBits_bitsOfZMod,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hy : y = bitsOfZMod (d + dB)
  · by_cases hr : r' = r
    · subst hy; subst hr
      simp [zmodOfBits_bitsOfZMod]
    · simp [hy, hr]
  · simp [hy]

private lemma steane_eq_slice3 {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2))
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB FP FB HP HB GP GB ψ wP wB =
      act (Matrix.kronecker (rowPauli (decB wB) (decP wP)) (1 : Matrix R R ℂ))
        (slice3 (HP * hadamardN n) HB wP wB
          (act (liftDataBit (R := R) (GB * transCnot n))
            (act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap))
              (tensorVec ψ (tensorVec (act FP (cssZeroState C2)) (act FB (cssPlusState C1))))))) :=
  rfl

private lemma steaneECOutput_pauli_mem {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (F : Finset (Fin n))
    (aFP bFP aFB bFB aHP bHP aHB bHB aGP1 bGP1 aGP2 bGP2 aGB1 bGB1 aGB2 bGB2 : Fin n → ZMod 2)
    (haFP : SuppIn F aFP) (hbFP : SuppIn F bFP)
    (haFB : SuppIn F aFB) (hbFB : SuppIn F bFB)
    (haHP : SuppIn F aHP) (hbHP : SuppIn F bHP)
    (haHB : SuppIn F aHB) (hbHB : SuppIn F bHB)
    (haGP1 : SuppIn F aGP1) (hbGP1 : SuppIn F bGP1)
    (haGP2 : SuppIn F aGP2) (hbGP2 : SuppIn F bGP2)
    (haGB1 : SuppIn F aGB1) (hbGB1 : SuppIn F bGB1)
    (haGB2 : SuppIn F aGB2) (hbGB2 : SuppIn F bGB2)
    (x : Fin n → ZMod 2) (r : R) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB
      (rowPauli aFP bFP) (rowPauli aFB bFB) (rowPauli aHP bHP) (rowPauli aHB bHB)
      (Matrix.kronecker (rowPauli aGP1 bGP1) (rowPauli aGP2 bGP2))
      (Matrix.kronecker (rowPauli aGB1 bGB1) (rowPauli aGB2 bGB2))
      (ket (bitsOfZMod x, r)) wP wB ∈
      errorSpaceWithRef R (cssCode C1 C2) F := by
  classical
  let FP := rowPauli aFP bFP
  let FB := rowPauli aFB bFB
  let HP := rowPauli aHP bHP
  let HB := rowPauli aHB bHB
  let GP := Matrix.kronecker (rowPauli aGP1 bGP1) (rowPauli aGP2 bGP2)
  let GB := Matrix.kronecker (rowPauli aGB1 bGB1) (rowPauli aGB2 bGB2)
  have hs0 : tensorVec (ket (bitsOfZMod x, r))
      (tensorVec (act FP (cssZeroState C2)) (act FB (cssPlusState C1))) =
      ∑ w : binDual C2, ∑ u : C1,
        (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB)) •
          ket ((bitsOfZMod x, r), (bitsOfZMod (w.1 + aFP), bitsOfZMod (u.1 + aFB))) := by
    dsimp only [FP, FB, cssZeroState, cssCosetState, cssPlusState]
    simp_rw [zero_add, act_sum, act_rowPauli_ket, tensorVec_sum_left, tensorVec_sum_right,
      tensorVec_smul_left, tensorVec_smul_right, tensorVec_ket, smul_smul]
  have hstep1 : ∀ w : binDual C2, ∀ u : C1,
      act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap))
        (ket ((bitsOfZMod x, r), (bitsOfZMod (w.1 + aFP), bitsOfZMod (u.1 + aFB)))) =
      (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) •
        ket ((bitsOfZMod (x + (w.1 + aFP) + aGP1), r),
          (bitsOfZMod ((w.1 + aFP) + aGP2), bitsOfZMod (u.1 + aFB))) := by
    intro w u
    refine act_liftDataPhase_ket _ _ _ _ _ _ _ _ fun y1 y2 => ?_
    rw [mul_transCnot_swap_bitsOfZMod]
    exact kronecker_rowPauli_bitsOfZMod aGP1 bGP1 aGP2 bGP2 (x + (w.1 + aFP)) (w.1 + aFP) y1 y2
  have hstep2 : ∀ w : binDual C2, ∀ u : C1,
      act (liftDataBit (R := R) (GB * transCnot n))
        (ket ((bitsOfZMod (x + (w.1 + aFP) + aGP1), r),
          (bitsOfZMod ((w.1 + aFP) + aGP2), bitsOfZMod (u.1 + aFB)))) =
      (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
        chi (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) •
        ket ((bitsOfZMod ((x + (w.1 + aFP) + aGP1) + aGB1), r),
          (bitsOfZMod ((w.1 + aFP) + aGP2),
            bitsOfZMod ((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2))) := by
    intro w u
    refine act_liftDataBit_ket _ _ _ _ _ _ _ _ fun y1 y3 => ?_
    rw [mul_transCnot_bitsOfZMod]
    exact kronecker_rowPauli_bitsOfZMod aGB1 bGB1 aGB2 bGB2
      (x + (w.1 + aFP) + aGP1) ((u.1 + aFB) + (x + (w.1 + aFP) + aGP1)) y1 y3
  rw [steane_eq_slice3]
  change act (Matrix.kronecker (rowPauli (decB wB) (decP wP)) (1 : Matrix R R ℂ))
    (slice3 (HP * hadamardN n) HB wP wB
      (act (liftDataBit (R := R) (GB * transCnot n))
        (act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap))
          (tensorVec (ket (bitsOfZMod x, r))
            (tensorVec (act FP (cssZeroState C2)) (act FB (cssPlusState C1))))))) ∈
    errorSpaceWithRef R (cssCode C1 C2) F
  rw [hs0]
  have hs1 :
      act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap))
        (∑ w : binDual C2, ∑ u : C1,
          (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB)) •
            ket ((bitsOfZMod x, r), (bitsOfZMod (w.1 + aFP), bitsOfZMod (u.1 + aFB)))) =
      ∑ w : binDual C2, ∑ u : C1,
        ((chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB)) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2))) •
          ket ((bitsOfZMod (x + (w.1 + aFP) + aGP1), r),
            (bitsOfZMod ((w.1 + aFP) + aGP2), bitsOfZMod (u.1 + aFB))) := by
    simp_rw [act_sum, act_smul, hstep1, smul_smul]
  rw [hs1]
  have hs2 :
      act (liftDataBit (R := R) (GB * transCnot n))
        (∑ w : binDual C2, ∑ u : C1,
          ((chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB)) *
            (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2))) •
            ket ((bitsOfZMod (x + (w.1 + aFP) + aGP1), r),
              (bitsOfZMod ((w.1 + aFP) + aGP2), bitsOfZMod (u.1 + aFB)))) =
      ∑ w : binDual C2, ∑ u : C1,
        (((chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB)) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2))) *
          (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
            chi (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2))) •
          ket ((bitsOfZMod ((x + (w.1 + aFP) + aGP1) + aGB1), r),
            (bitsOfZMod ((w.1 + aFP) + aGP2),
              bitsOfZMod ((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2))) := by
    simp_rw [act_sum, act_smul, hstep2, smul_smul]
  rw [hs2]
  simp_rw [slice3_sum, slice3_smul, slice3_ket, smul_smul]
  simp_rw [act_sum, act_smul, act_decoder_ket, smul_smul]
  let eX : Fin n → ZMod 2 := aFP + aGP1 + aGB1
  let eB : Fin n → ZMod 2 := aFB + aFP + aGP1 + aGB2 + aHB
  let eP : Fin n → ZMod 2 := aFP + aGP2
  let u0 : Fin n → ZMod 2 := wB + x + eB
  have hMB : ∀ w : binDual C2, ∀ u : C1,
      HB (bitsOfZMod wB) (bitsOfZMod ((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2)) =
        if u.1 = u0 + w.1 then chi (wB ⬝ᵥ bHB) else 0 := by
    intro w u
    change rowPauli aHB bHB (bitsOfZMod wB)
      (bitsOfZMod ((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2)) = _
    rw [rowPauli_apply, zmodOfBits_bitsOfZMod, zmodOfBits_bitsOfZMod]
    have hiff : bitsOfZMod wB =
        bitsOfZMod (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) + aHB) ↔
        u.1 = u0 + w.1 := by
      rw [bitsOfZMod_eq_iff, zmod2_eq_iff_add_eq_zero wB _, zmod2_eq_iff_add_eq_zero u.1 _]
      have hab : wB + (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) + aHB) =
          u.1 + (u0 + w.1) := by
        dsimp [u0, eB]; abel
      rw [hab]
    exact if_congr hiff rfl rfl
  simp_rw [hMB, HP, rowPauli_mul_hadamardN_bitsOfZMod]
  by_cases hu0 : u0 ∈ C1
  · have hsum_u : ∀ w : binDual C2,
      (∑ u : C1,
        (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) *
          (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
            chi (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) *
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) *
            chi (((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP)) *
            if u.1 = u0 + w.1 then chi (wB ⬝ᵥ bHB) else 0) *
          chi ((((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB) ⬝ᵥ decP wP)) •
        tensorVec (ket (bitsOfZMod (((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB))) (ket r)) =
      (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi (((u0 + w.1) + aFB) ⬝ᵥ bFB) *
        (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) *
        (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
          chi ((((u0 + w.1) + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) *
        ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) *
          chi (((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP)) * chi (wB ⬝ᵥ bHB)) *
        chi ((((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB) ⬝ᵥ decP wP)) •
        tensorVec (ket (bitsOfZMod (((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB))) (ket r) := by
      intro w
      let u_star : C1 := ⟨u0 + w.1, C1.add_mem hu0 (hC w.2)⟩
      rw [Finset.sum_eq_single u_star]
      · have heq : u_star.1 = u0 + w.1 := rfl
        rw [if_pos heq]
      · intro u _ hu
        have hne : u.1 ≠ u0 + w.1 := fun h => hu (Subtype.ext h)
        rw [if_neg hne, mul_zero, mul_zero, zero_mul, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ u_star) h
    simp_rw [hsum_u]
    let u1 : Fin n → ZMod 2 := u0 + (wB + decB wB)
    have hwB_mem : wB + decB wB ∈ C1 := by
      refine mem_of_forall_mem_binDual C1 (wB + decB wB) fun h hh => ?_
      rw [dotProduct_add, hdecB wB h hh, CharTwo.add_self_eq_zero]
    have hu1 : u1 ∈ C1 := C1.add_mem hu0 hwB_mem
    let eXtot : Fin n → ZMod 2 := eB + eX
    let eZ : Fin n → ZMod 2 := bFP + bFB + bGP1 + bGP2 + bGB1 + aHP
    have heXtot : SuppIn F eXtot := by
      dsimp [eXtot, eB, eX]
      exact suppIn_add
        (suppIn_add (suppIn_add (suppIn_add (suppIn_add haFB haFP) haGP1) haGB2) haHB)
        (suppIn_add (suppIn_add haFP haGP1) haGB1)
    have heZ : SuppIn F eZ := by
      dsimp [eZ]
      exact suppIn_add (suppIn_add (suppIn_add (suppIn_add (suppIn_add hbFP hbFB) hbGP1) hbGP2) hbGB1) haHP
    have hket_eq : ∀ w : binDual C2,
        ((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB = (u1 + w.1) + eXtot := by
      intro w
      have hx : x = u0 + wB + eB := by
        dsimp [u0]
        rw [add_assoc wB x eB, add_comm wB (x + eB), zmod2_add_cancel_right, zmod2_add_cancel_right]
      rw [hx]
      dsimp [u1, eXtot, eX]
      abel
    let c0 : ℂ :=
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
        chi (aFP ⬝ᵥ bFP) *
        chi ((u0 + aFB) ⬝ᵥ bFB) *
        chi ((x + aFP + aGP1) ⬝ᵥ bGP1) *
        chi ((aFP + aGP2) ⬝ᵥ bGP2) *
        chi ((x + aFP + aGP1 + aGB1) ⬝ᵥ bGB1) *
        chi ((u0 + aFB + x + aFP + aGP1 + aGB2) ⬝ᵥ bGB2) *
        chi (wP ⬝ᵥ bHP) *
        chi ((aFP + aGP2) ⬝ᵥ (wP + aHP)) *
        chi (wB ⬝ᵥ bHB) *
        chi ((u1 + eXtot) ⬝ᵥ decP wP) *
        chi ((u1 + eXtot) ⬝ᵥ eZ)
    have hcoeff_eq : ∀ w : binDual C2,
        chi ((w.1 + aFP) ⬝ᵥ bFP) * chi (((u0 + w.1) + aFB) ⬝ᵥ bFB) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) *
          (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
            chi ((((u0 + w.1) + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) *
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) *
            chi (((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP)) * chi (wB ⬝ᵥ bHB)) *
          chi ((((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB) ⬝ᵥ decP wP) =
        c0 * chi (((u1 + w.1) + eXtot) ⬝ᵥ eZ) := by
      intro w
      rw [hket_eq w]
      have hcancel_w : ((u0 + w.1) + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2 =
          u0 + aFB + x + aFP + aGP1 + aGB2 := by
        rw [show ((u0 + w.1) + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2 =
            (w.1 + w.1) + (u0 + aFB + x + aFP + aGP1 + aGB2) by abel,
          zmod2_add_self, zero_add]
      rw [hcancel_w]
      have hw1 : (w.1 + aFP) ⬝ᵥ bFP = aFP ⬝ᵥ bFP + w.1 ⬝ᵥ bFP := by
        rw [add_dotProduct, add_comm]
      have hw2 : ((u0 + w.1) + aFB) ⬝ᵥ bFB = (u0 + aFB) ⬝ᵥ bFB + w.1 ⬝ᵥ bFB := by
        rw [show (u0 + w.1) + aFB = (u0 + aFB) + w.1 by abel, add_dotProduct]
      have hw3 : (x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1 = (x + aFP + aGP1) ⬝ᵥ bGP1 + w.1 ⬝ᵥ bGP1 := by
        rw [show x + (w.1 + aFP) + aGP1 = (x + aFP + aGP1) + w.1 by abel, add_dotProduct]
      have hw4 : ((w.1 + aFP) + aGP2) ⬝ᵥ bGP2 = (aFP + aGP2) ⬝ᵥ bGP2 + w.1 ⬝ᵥ bGP2 := by
        rw [show (w.1 + aFP) + aGP2 = (aFP + aGP2) + w.1 by abel, add_dotProduct]
      have hw5 : ((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1 =
          (x + aFP + aGP1 + aGB1) ⬝ᵥ bGB1 + w.1 ⬝ᵥ bGB1 := by
        rw [show (x + (w.1 + aFP) + aGP1) + aGB1 = (x + aFP + aGP1 + aGB1) + w.1 by abel,
          add_dotProduct]
      have hw6 : ((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP) =
          (aFP + aGP2) ⬝ᵥ (wP + aHP) + (w.1 ⬝ᵥ wP + w.1 ⬝ᵥ aHP) := by
        rw [show (w.1 + aFP) + aGP2 = (aFP + aGP2) + w.1 by abel, add_dotProduct, dotProduct_add w.1]
      have hw7 : ((u1 + w.1) + eXtot) ⬝ᵥ decP wP = (u1 + eXtot) ⬝ᵥ decP wP + w.1 ⬝ᵥ wP := by
        rw [show (u1 + w.1) + eXtot = (u1 + eXtot) + w.1 by abel, add_dotProduct,
          hdecP wP w.1 w.2]
      have hw8 : ((u1 + w.1) + eXtot) ⬝ᵥ eZ =
          (u1 + eXtot) ⬝ᵥ eZ +
            (w.1 ⬝ᵥ bFP + w.1 ⬝ᵥ bFB + w.1 ⬝ᵥ bGP1 + w.1 ⬝ᵥ bGP2 + w.1 ⬝ᵥ bGB1 + w.1 ⬝ᵥ aHP) := by
        rw [show (u1 + w.1) + eXtot = (u1 + eXtot) + w.1 by abel, add_dotProduct]
        dsimp [eZ]
        simp only [dotProduct_add, add_assoc]
      rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8]
      simp only [chi_add, c0]
      have hself1 : chi ((u1 + eXtot) ⬝ᵥ eZ) * chi ((u1 + eXtot) ⬝ᵥ eZ) = 1 :=
        chi_mul_self _
      have hself2 : chi (w.1 ⬝ᵥ wP) * chi (w.1 ⬝ᵥ wP) = 1 :=
        chi_mul_self _
      linear_combination
        ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          chi (aFP ⬝ᵥ bFP) * chi ((u0 + aFB) ⬝ᵥ bFB) *
          chi ((x + aFP + aGP1) ⬝ᵥ bGP1) * chi ((aFP + aGP2) ⬝ᵥ bGP2) *
          chi ((x + aFP + aGP1 + aGB1) ⬝ᵥ bGB1) *
          chi ((u0 + aFB + x + aFP + aGP1 + aGB2) ⬝ᵥ bGB2) *
          chi (wP ⬝ᵥ bHP) * chi ((aFP + aGP2) ⬝ᵥ (wP + aHP)) *
          chi (wB ⬝ᵥ bHB) * chi ((u1 + eXtot) ⬝ᵥ decP wP) *
          chi (w.1 ⬝ᵥ bFP) * chi (w.1 ⬝ᵥ bFB) * chi (w.1 ⬝ᵥ bGP1) *
          chi (w.1 ⬝ᵥ bGP2) * chi (w.1 ⬝ᵥ bGB1) * chi (w.1 ⬝ᵥ aHP)) * hself2 -
        ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          chi (aFP ⬝ᵥ bFP) * chi ((u0 + aFB) ⬝ᵥ bFB) *
          chi ((x + aFP + aGP1) ⬝ᵥ bGP1) * chi ((aFP + aGP2) ⬝ᵥ bGP2) *
          chi ((x + aFP + aGP1 + aGB1) ⬝ᵥ bGB1) *
          chi ((u0 + aFB + x + aFP + aGP1 + aGB2) ⬝ᵥ bGB2) *
          chi (wP ⬝ᵥ bHP) * chi ((aFP + aGP2) ⬝ᵥ (wP + aHP)) *
          chi (wB ⬝ᵥ bHB) * chi ((u1 + eXtot) ⬝ᵥ decP wP) *
          chi (w.1 ⬝ᵥ bFP) * chi (w.1 ⬝ᵥ bFB) * chi (w.1 ⬝ᵥ bGP1) *
          chi (w.1 ⬝ᵥ bGP2) * chi (w.1 ⬝ᵥ bGB1) * chi (w.1 ⬝ᵥ aHP)) * hself1
    have hterm_eq : ∀ w : binDual C2,
        (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi (((u0 + w.1) + aFB) ⬝ᵥ bFB) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) *
          (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
            chi ((((u0 + w.1) + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) *
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) *
            chi (((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP)) * chi (wB ⬝ᵥ bHB)) *
          chi ((((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB) ⬝ᵥ decP wP)) •
          tensorVec (ket (bitsOfZMod (((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB))) (ket r) =
        c0 • tensorVec (act (rowPauli eXtot eZ) (ket (bitsOfZMod (u1 + w.1)))) (ket r) := by
      intro w
      rw [hcoeff_eq w, hket_eq w, act_rowPauli_ket, tensorVec_smul_left, smul_smul]
    simp_rw [hterm_eq, ← Finset.smul_sum, ← tensorVec_sum_left, ← act_sum]
    change c0 • tensorVec (act (rowPauli eXtot eZ) (cssCosetState C2 u1)) (ket r) ∈
      errorSpaceWithRef R (cssCode C1 C2) F
    refine Submodule.smul_mem _ c0 (Submodule.subset_span ?_)
    refine ⟨act (rowPauli eXtot eZ) (cssCosetState C2 u1), Submodule.subset_span ?_, ket r, rfl⟩
    exact ⟨rowPauli eXtot eZ, cssCosetState C2 u1, actsWithin_rowPauli F eXtot eZ heXtot heZ,
      Submodule.subset_span ⟨⟨u1, hu1⟩, rfl⟩, rfl⟩
  · have hzero : ∀ w : binDual C2, ∀ u : C1, u.1 ≠ u0 + w.1 := by
      intro w u h
      apply hu0
      have h1 : u0 = u.1 + w.1 := by
        rw [h, zmod2_add_cancel_right]
      rw [h1]
      exact C1.add_mem u.2 (hC w.2)
    have hsum0 : ∀ w : binDual C2, ∀ u : C1,
        (chi ((w.1 + aFP) ⬝ᵥ bFP) * chi ((u.1 + aFB) ⬝ᵥ bFB) *
          (chi ((x + (w.1 + aFP) + aGP1) ⬝ᵥ bGP1) * chi (((w.1 + aFP) + aGP2) ⬝ᵥ bGP2)) *
          (chi (((x + (w.1 + aFP) + aGP1) + aGB1) ⬝ᵥ bGB1) *
            chi (((u.1 + aFB) + (x + (w.1 + aFP) + aGP1) + aGB2) ⬝ᵥ bGB2)) *
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * chi (wP ⬝ᵥ bHP) *
            chi (((w.1 + aFP) + aGP2) ⬝ᵥ (wP + aHP)) *
            if u.1 = u0 + w.1 then chi (wB ⬝ᵥ bHB) else 0) *
          chi ((((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB) ⬝ᵥ decP wP)) •
        tensorVec (ket (bitsOfZMod (((x + (w.1 + aFP) + aGP1) + aGB1) + decB wB))) (ket r) = 0 := by
      intro w u
      rw [if_neg (hzero w u), mul_zero, mul_zero, zero_mul, zero_smul]
    simp_rw [hsum0, Finset.sum_const_zero]
    exact Submodule.zero_mem _

private lemma liftDataPhase_zero {n : ℕ} {R : Type*} [DecidableEq R] :
    liftDataPhase (R := R) (0 : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) = 0 := by
  ext p q; simp [liftDataPhase]

private lemma liftDataPhase_add {n : ℕ} {R : Type*} [DecidableEq R]
    (M1 M2 : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    liftDataPhase (R := R) (M1 + M2) = liftDataPhase M1 + liftDataPhase M2 := by
  ext p q; simp [liftDataPhase, ite_add_zero]

private lemma liftDataPhase_smul {n : ℕ} {R : Type*} [DecidableEq R] (c : ℂ)
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    liftDataPhase (R := R) (c • M) = c • liftDataPhase M := by
  ext p q; simp [liftDataPhase, mul_ite]

private lemma liftDataBit_zero {n : ℕ} {R : Type*} [DecidableEq R] :
    liftDataBit (R := R) (0 : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) = 0 := by
  ext p q; simp [liftDataBit]

private lemma liftDataBit_add {n : ℕ} {R : Type*} [DecidableEq R]
    (M1 M2 : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    liftDataBit (R := R) (M1 + M2) = liftDataBit M1 + liftDataBit M2 := by
  ext p q; simp [liftDataBit, ite_add_zero]

private lemma liftDataBit_smul {n : ℕ} {R : Type*} [DecidableEq R] (c : ℂ)
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    liftDataBit (R := R) (c • M) = c • liftDataBit M := by
  ext p q; simp [liftDataBit, mul_ite]

private lemma kronecker_zero_left {ι κ : Type*} (B : Matrix κ κ ℂ) :
    Matrix.kronecker (0 : Matrix ι ι ℂ) B = 0 := by
  ext p q; simp [Matrix.kronecker]

private lemma kronecker_add_left {ι κ : Type*} (A1 A2 : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Matrix.kronecker (A1 + A2) B = Matrix.kronecker A1 B + Matrix.kronecker A2 B := by
  ext p q; simp [Matrix.kronecker, add_mul]

private lemma kronecker_smul_left {ι κ : Type*} (c : ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Matrix.kronecker (c • A) B = c • Matrix.kronecker A B := by
  ext p q; simp [Matrix.kronecker, mul_assoc]

private lemma kronecker_zero_right {ι κ : Type*} (A : Matrix ι ι ℂ) :
    Matrix.kronecker A (0 : Matrix κ κ ℂ) = 0 := by
  ext p q; simp [Matrix.kronecker]

private lemma kronecker_add_right {ι κ : Type*} (A : Matrix ι ι ℂ) (B1 B2 : Matrix κ κ ℂ) :
    Matrix.kronecker A (B1 + B2) = Matrix.kronecker A B1 + Matrix.kronecker A B2 := by
  ext p q; simp [Matrix.kronecker, mul_add]

private lemma kronecker_smul_right {ι κ : Type*} (c : ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Matrix.kronecker A (c • B) = c • Matrix.kronecker A B := by
  ext p q; simp [Matrix.kronecker, mul_left_comm]

private lemma euclid_sum_apply {α ι : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ ι) (p : ι) :
    (∑ x ∈ s, f x) p = ∑ x ∈ s, f x p := by
  classical
  induction' s using Finset.cons_induction with a t ha ih
  · rfl
  · rw [Finset.sum_cons, Finset.sum_cons, PiLp.add_apply, ih]

private lemma psi_eq_sum_ket {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (ψ : EuclideanSpace ℂ (Qubits n × R)) :
    ψ = ∑ p : (Fin n → ZMod 2) × R,
      ψ (bitsOfZMod p.1, p.2) • ket (bitsOfZMod p.1, p.2) := by
  ext ⟨y, r⟩
  rw [euclid_sum_apply]
  rw [Finset.sum_eq_single (zmodOfBits y, r)]
  · rw [PiLp.smul_apply, ket_apply, bitsOfZMod_zmodOfBits, if_pos rfl, smul_eq_mul, mul_one]
  · rintro ⟨x, r'⟩ _ hne
    have hne' : (y, r) ≠ (bitsOfZMod x, r') := by
      rintro ⟨rfl, rfl⟩
      exact hne (Prod.ext (zmodOfBits_bitsOfZMod x).symm rfl)
    rw [PiLp.smul_apply, ket_apply, if_neg hne', smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma slice3_zero_left {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 0 MB wP wB s2 = 0 := by
  ext p
  simp only [slice3, kronecker_zero_left, kronecker_zero_right, zero_act]
  rfl

private lemma slice3_add_left {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (X Y MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 (X + Y) MB wP wB s2 = slice3 X MB wP wB s2 + slice3 Y MB wP wB s2 := by
  ext p
  simp only [slice3, kronecker_add_left, kronecker_add_right, add_act, PiLp.add_apply]

private lemma slice3_smul_left {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (c : ℂ) (X MB : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 (c • X) MB wP wB s2 = c • slice3 X MB wP wB s2 := by
  ext p
  simp only [slice3, kronecker_smul_left, kronecker_smul_right, smul_act, PiLp.smul_apply]

private lemma slice3_zero_right {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP 0 wP wB s2 = 0 := by
  ext p
  simp only [slice3, kronecker_zero_right, zero_act]
  rfl

private lemma slice3_add_right {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (MP X Y : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP (X + Y) wP wB s2 = slice3 MP X wP wB s2 + slice3 MP Y wP wB s2 := by
  ext p
  simp only [slice3, kronecker_add_right, add_act, PiLp.add_apply]

private lemma slice3_smul_right {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (c : ℂ) (MP X : Matrix (Qubits n) (Qubits n) ℂ) (wP wB : Fin n → ZMod 2)
    (s2 : EuclideanSpace ℂ ((Qubits n × R) × (Qubits n × Qubits n))) :
    slice3 MP (c • X) wP wB s2 = c • slice3 MP X wP wB s2 := by
  ext p
  simp only [slice3, kronecker_smul_right, smul_act, PiLp.smul_apply]

private lemma steaneECOutput_G_mem {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (F gP gB : Finset (Fin n)) (hgP : gP ⊆ F) (hgB : gB ⊆ F)
    (aFP bFP aFB bFB aHP bHP aHB bHB : Fin n → ZMod 2)
    (haFP : SuppIn F aFP) (hbFP : SuppIn F bFP)
    (haFB : SuppIn F aFB) (hbFB : SuppIn F bFB)
    (haHP : SuppIn F aHP) (hbHP : SuppIn F bHP)
    (haHB : SuppIn F aHB) (hbHB : SuppIn F bHB)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hGP : ActsWithinPair gP GP) (hGB : ActsWithinPair gB GB)
    (x : Fin n → ZMod 2) (r : R) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB
      (rowPauli aFP bFP) (rowPauli aFB bFB) (rowPauli aHP bHP) (rowPauli aHB bHB)
      GP GB (ket (bitsOfZMod x, r)) wP wB ∈
      errorSpaceWithRef R (cssCode C1 C2) F := by
  let V := errorSpaceWithRef R (cssCode C1 C2) F
  let FP := rowPauli aFP bFP
  let FB := rowPauli aFB bFB
  let HP := rowPauli aHP bHP
  let HB := rowPauli aHB bHB
  let ψ := ket (bitsOfZMod x, r)
  refine actsWithinPair_span V F gP hgP
    (fun X => steaneECOutput C1 C2 decP decB FP FB HP HB X GB ψ wP wB)
    (by rw [steane_eq_slice3, zero_mul, liftDataPhase_zero, zero_act, act_zero, slice3_zero, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, add_mul, liftDataPhase_add, add_act, act_add, slice3_add, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, smul_mul_assoc, liftDataPhase_smul, smul_act, act_smul, slice3_smul, act_smul])
    ?_ hGP
  intro aGP1 bGP1 aGP2 bGP2 haGP1 hbGP1 haGP2 hbGP2
  let GP' := Matrix.kronecker (rowPauli aGP1 bGP1) (rowPauli aGP2 bGP2)
  refine actsWithinPair_span V F gB hgB
    (fun X => steaneECOutput C1 C2 decP decB FP FB HP HB GP' X ψ wP wB)
    (by rw [steane_eq_slice3, zero_mul, liftDataBit_zero, zero_act, slice3_zero, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, add_mul, liftDataBit_add, add_act, slice3_add, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, smul_mul_assoc, liftDataBit_smul, smul_act, slice3_smul, act_smul])
    ?_ hGB
  intro aGB1 bGB1 aGB2 bGB2 haGB1 hbGB1 haGB2 hbGB2
  exact steaneECOutput_pauli_mem C1 C2 hC decP decB hdecP hdecB F
    aFP bFP aFB bFB aHP bHP aHB bHB aGP1 bGP1 aGP2 bGP2 aGB1 bGB1 aGB2 bGB2
    haFP hbFP haFB hbFB haHP hbHP haHB hbHB haGP1 hbGP1 haGP2 hbGP2 haGB1 hbGB1 haGB2 hbGB2
    x r wP wB

private lemma steaneECOutput_FH_mem {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (F fP fB gP gB hP hB : Finset (Fin n))
    (hfP : fP ⊆ F) (hfB : fB ⊆ F) (hgP : gP ⊆ F) (hgB : gB ⊆ F) (hhP : hP ⊆ F) (hhB : hB ⊆ F)
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hFP : ActsWithin fP FP) (hFB : ActsWithin fB FB)
    (hGP : ActsWithinPair gP GP) (hGB : ActsWithinPair gB GB)
    (hHP : ActsWithin hP HP) (hHB : ActsWithin hB HB)
    (x : Fin n → ZMod 2) (r : R) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB FP FB HP HB GP GB (ket (bitsOfZMod x, r)) wP wB ∈
      errorSpaceWithRef R (cssCode C1 C2) F := by
  let V := errorSpaceWithRef R (cssCode C1 C2) F
  let ψ := ket (bitsOfZMod x, r)
  refine actsWithin_span V F fP hfP
    (fun X => steaneECOutput C1 C2 decP decB X FB HP HB GP GB ψ wP wB)
    (by rw [steane_eq_slice3, zero_act, tensorVec_zero_left, tensorVec_zero_right, act_zero, act_zero, slice3_zero, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, add_act, tensorVec_add_left, tensorVec_add_right, act_add, act_add, slice3_add, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, smul_act, tensorVec_smul_left, tensorVec_smul_right, act_smul, act_smul, slice3_smul, act_smul])
    ?_ hFP
  intro aFP bFP haFP hbFP
  let FP' := rowPauli aFP bFP
  refine actsWithin_span V F fB hfB
    (fun X => steaneECOutput C1 C2 decP decB FP' X HP HB GP GB ψ wP wB)
    (by rw [steane_eq_slice3, zero_act, tensorVec_zero_right, tensorVec_zero_right, act_zero, act_zero, slice3_zero, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, add_act, tensorVec_add_right, tensorVec_add_right, act_add, act_add, slice3_add, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, smul_act, tensorVec_smul_right, tensorVec_smul_right, act_smul, act_smul, slice3_smul, act_smul])
    ?_ hFB
  intro aFB bFB haFB hbFB
  let FB' := rowPauli aFB bFB
  refine actsWithin_span V F hP hhP
    (fun X => steaneECOutput C1 C2 decP decB FP' FB' X HB GP GB ψ wP wB)
    (by rw [steane_eq_slice3, zero_mul, slice3_zero_left, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, add_mul, slice3_add_left, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, smul_mul_assoc, slice3_smul_left, act_smul])
    ?_ hHP
  intro aHP bHP haHP hbHP
  let HP' := rowPauli aHP bHP
  refine actsWithin_span V F hB hhB
    (fun X => steaneECOutput C1 C2 decP decB FP' FB' HP' X GP GB ψ wP wB)
    (by rw [steane_eq_slice3, slice3_zero_right, act_zero])
    (fun X Y => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, slice3_add_right, act_add])
    (fun c X => by rw [steane_eq_slice3, steane_eq_slice3, slice3_smul_right, act_smul])
    ?_ hHB
  intro aHB bHB haHB hbHB
  exact steaneECOutput_G_mem C1 C2 hC decP decB hdecP hdecB F gP gB hgP hgB
    aFP bFP aFB bFB aHP bHP aHB bHB haFP hbFP haFB hbFB haHP hbHP haHB hbHB
    GP GB hGP hGB x r wP wB

theorem solution {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (fP fB gP gB hP hB : Finset (Fin n))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hFP : ActsWithin fP FP) (hFB : ActsWithin fB FB)
    (hGP : ActsWithinPair gP GP) (hGB : ActsWithinPair gB GB)
    (hHP : ActsWithin hP HP) (hHB : ActsWithin hB HB)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB FP FB HP HB GP GB ψ wP wB ∈
        errorSpaceWithRef R (cssCode C1 C2) (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB) ∧
      (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB).card ≤
        fP.card + fB.card + gP.card + gB.card + hP.card + hB.card := by
  let F := fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB
  let V := errorSpaceWithRef R (cssCode C1 C2) F
  refine ⟨?_, ?_⟩
  · have hfP : fP ⊆ F := by intro q hq; simp [F, hq]
    have hfB : fB ⊆ F := by intro q hq; simp [F, hq]
    have hgP : gP ⊆ F := by intro q hq; simp [F, hq]
    have hgB : gB ⊆ F := by intro q hq; simp [F, hq]
    have hhP : hP ⊆ F := by intro q hq; simp [F, hq]
    have hhB : hB ⊆ F := by intro q hq; simp [F, hq]
    rw [psi_eq_sum_ket ψ]
    have hlin := mem_submodule_of_linear V
      (fun φ => steaneECOutput C1 C2 decP decB FP FB HP HB GP GB φ wP wB)
      (by rw [steane_eq_slice3, tensorVec_zero_left, act_zero, act_zero, slice3_zero, act_zero])
      (fun u v => by rw [steane_eq_slice3, steane_eq_slice3, steane_eq_slice3, tensorVec_add_left, act_add, act_add, slice3_add, act_add])
      (fun c u => by rw [steane_eq_slice3, steane_eq_slice3, tensorVec_smul_left, act_smul, act_smul, slice3_smul, act_smul])
      (Finset.univ : Finset ((Fin n → ZMod 2) × R))
      (fun p => ψ (bitsOfZMod p.1, p.2))
      (fun p => ket (bitsOfZMod p.1, p.2))
      (fun ⟨x, r⟩ _ => steaneECOutput_FH_mem C1 C2 hC decP decB hdecP hdecB F fP fB gP gB hP hB
        hfP hfB hgP hgB hhP hhB FP FB HP HB GP GB hFP hFB hGP hGB hHP hHB x r wP wB)
    exact hlin
  · have h1 := Finset.card_union_le (fP ∪ fB ∪ gP ∪ gB ∪ hP) hB
    have h2 := Finset.card_union_le (fP ∪ fB ∪ gP ∪ gB) hP
    have h3 := Finset.card_union_le (fP ∪ fB ∪ gP) gB
    have h4 := Finset.card_union_le (fP ∪ fB) gP
    have h5 := Finset.card_union_le fP fB
    omega

end
