-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.pauli_four_outcome_povm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:47:48.424982+00:00
-- url     : https://prove2.me/submissions/d223969f-72ec-4bd4-bffa-618b81ad1571

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate ComplexOrder

theorem g66f_X : pauliXFin = !![0,1;1,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliXFin, QAlgorithms.pauliX]
theorem g66f_Z : pauliZFin = !![1,0;0,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZFin, QAlgorithms.pauliZ, Matrix.diagonal]

def g66f_F (s x z : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if x then !![0, (if s then -1 else 1) * (if z then -1 else 1); (if s then -1 else 1), 0]
  else !![(if s then -1 else 1), 0; 0, (if s then -1 else 1) * (if z then -1 else 1)]

theorem g66f_Fmul (s x z s' x' z' : Bool) :
    g66f_F s x z * g66f_F s' x' z' = g66f_F (xor s (xor s' (z && x'))) (xor x x') (xor z z') := by
  cases s <;> cases x <;> cases z <;> cases s' <;> cases x' <;> cases z' <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [g66f_F, Matrix.mul_apply, Fin.sum_univ_two])

theorem g66f_Fstar (s x z : Bool) :
    star (g66f_F s x z) = g66f_F (xor s (x && z)) x z := by
  cases s <;> cases x <;> cases z <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [g66f_F, Matrix.star_apply])

theorem g66f_ne1 : ((1:ℂ) = -1) = False := by
  rw [eq_iff_iff, iff_false]; norm_num
theorem g66f_ne1' : ((-1:ℂ) = 1) = False := by
  rw [eq_iff_iff, iff_false]; norm_num

theorem g66f_Finj (s x z s' x' z' : Bool) (h : g66f_F s x z = g66f_F s' x' z') :
    s = s' ∧ x = x' ∧ z = z' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  cases s <;> cases x <;> cases z <;> cases s' <;> cases x' <;> cases z' <;>
    simp [g66f_F, g66f_ne1, g66f_ne1'] at h00 h01 h10 h11 ⊢

theorem g66f_sb_mul {d c : ℕ} (A A' : Matrix (Fin d) (Fin d) ℂ) (B B' : Matrix (Fin c) (Fin c) ℂ) :
    sumBlock A B * sumBlock A' B' = sumBlock (A * A') (B * B') := by
  unfold sumBlock
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp

theorem g66f_sb_one {d c : ℕ} :
    sumBlock (1 : Matrix (Fin d) (Fin d) ℂ) (1 : Matrix (Fin c) (Fin c) ℂ) = 1 := by
  unfold sumBlock; rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem g66f_sb_star {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin c) (Fin c) ℂ) :
    (sumBlock A B).conjTranspose = sumBlock A.conjTranspose B.conjTranspose := by
  unfold sumBlock; rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]; simp

theorem g66f_sbZ : sumBlock pauliZFin pauliZFin = !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sumBlock, pauliZFin, QAlgorithms.pauliZ, finSumFinEquiv, Fin.addCases, Matrix.diagonal]
theorem g66f_sbX : sumBlock pauliXFin pauliXFin = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sumBlock, pauliXFin, QAlgorithms.pauliX, finSumFinEquiv, Fin.addCases]

theorem g66f_unit (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    qubitCompletion a b ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have ha : a * conj a = (Complex.normSq a : ℂ) := Complex.mul_conj a
  have hb : b * conj b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  have hR : Complex.normSq a + Complex.normSq b = 1 / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; exact hnorm
  have hC : ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) = 1 / 2 := by
    rw [hR]; push_cast; ring
  push_cast at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qubitCompletion, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply] <;>
    first | ring1 | linear_combination 2*ha + 2*hb + 2*hC

theorem g66f_DZ (a b : ℂ) :
    sumBlock pauliZFin pauliZFin * qubitCompletion a b = qubitCompletion a b * pauliRZ := by
  rw [g66f_sbZ]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [qubitCompletion, pauliRZ, Matrix.mul_apply, Fin.sum_univ_four]
theorem g66f_DX (a b : ℂ) :
    sumBlock pauliXFin pauliXFin * qubitCompletion a b = qubitCompletion a b * pauliRX := by
  rw [g66f_sbX]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [qubitCompletion, pauliRX, Matrix.mul_apply, Fin.sum_univ_four]

def g66f_Rm (a b : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (qubitCompletion a b).conjTranspose * sumBlock g g * qubitCompletion a b

section
variable (a b : ℂ) (hD : qubitCompletion a b * (qubitCompletion a b).conjTranspose = 1)
include hD

theorem g66f_hD' : (qubitCompletion a b).conjTranspose * qubitCompletion a b = 1 :=
  mul_eq_one_comm.mp hD

theorem g66f_Rm_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    g66f_Rm a b (g * h) = g66f_Rm a b g * g66f_Rm a b h := by
  unfold g66f_Rm
  rw [← g66f_sb_mul]
  set D := qubitCompletion a b
  calc D.conjTranspose * (sumBlock g g * sumBlock h h) * D
      = D.conjTranspose * sumBlock g g * 1 * sumBlock h h * D := by simp [Matrix.mul_assoc]
    _ = _ := by rw [← hD]; simp only [Matrix.mul_assoc]

theorem g66f_Rm_one : g66f_Rm a b 1 = 1 := by
  unfold g66f_Rm; rw [g66f_sb_one, Matrix.mul_one, g66f_hD' a b hD]

theorem g66f_Rm_X : g66f_Rm a b pauliXFin = pauliRX := by
  unfold g66f_Rm; rw [Matrix.mul_assoc, g66f_DX, ← Matrix.mul_assoc, g66f_hD' a b hD, Matrix.one_mul]
theorem g66f_Rm_Z : g66f_Rm a b pauliZFin = pauliRZ := by
  unfold g66f_Rm; rw [Matrix.mul_assoc, g66f_DZ, ← Matrix.mul_assoc, g66f_hD' a b hD, Matrix.one_mul]

theorem g66f_Rm_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (g66f_Rm a b g).conjTranspose = g66f_Rm a b g.conjTranspose := by
  unfold g66f_Rm
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, g66f_sb_star,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem g66f_Rm_unit (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    g66f_Rm a b g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hg ⊢
  rw [Matrix.star_eq_conjTranspose, g66f_Rm_star a b hD, ← g66f_Rm_mul a b hD,
    ← Matrix.star_eq_conjTranspose, hg, g66f_Rm_one a b hD]

theorem g66f_Q : qubitColumns a b =
    (!![1,0,0,0; 0,1,0,0] : Matrix (Fin 2) (Fin 4) ℂ) * qubitCompletion a b := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qubitCompletion, qubitColumns, Matrix.mul_apply, Fin.sum_univ_four]

theorem g66f_inter (g : Matrix (Fin 2) (Fin 2) ℂ) :
    g * qubitColumns a b = qubitColumns a b * g66f_Rm a b g := by
  have hP : (!![1,0,0,0; 0,1,0,0] : Matrix (Fin 2) (Fin 4) ℂ) * sumBlock g g =
      g * (!![1,0,0,0; 0,1,0,0] : Matrix (Fin 2) (Fin 4) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sumBlock, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, finSumFinEquiv,
        Fin.addCases]
  unfold g66f_Rm
  rw [g66f_Q a b hD]
  rw [show (!![1,0,0,0; 0,1,0,0] : Matrix (Fin 2) (Fin 4) ℂ) * qubitCompletion a b *
      ((qubitCompletion a b).conjTranspose * sumBlock g g * qubitCompletion a b) =
      (!![1,0,0,0; 0,1,0,0] : Matrix (Fin 2) (Fin 4) ℂ) *
        (qubitCompletion a b * (qubitCompletion a b).conjTranspose) * sumBlock g g *
          qubitCompletion a b by simp only [Matrix.mul_assoc], hD, Matrix.mul_one, hP,
    Matrix.mul_assoc]
end

theorem g66f_mono_mul (A B : Matrix (Fin 4) (Fin 4) ℂ) (hA : Monomial A) (hB : Monomial B) :
    Monomial (A * B) := by
  obtain ⟨pa, za, hza, hA⟩ := hA
  obtain ⟨pb, zb, hzb, hB⟩ := hB
  refine ⟨pb.trans pa, fun j => za (pb j) * zb j, fun j => by simp [hza, hzb], fun i j => ?_⟩
  rw [Matrix.mul_apply]
  simp_rw [hB, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hA]
  simp only [Equiv.trans_apply]
  by_cases h : i = pa (pb j) <;> simp [h, mul_comm]

theorem g66f_mono_one : Monomial (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨1, fun _ => 1, fun _ => by simp, fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩

theorem g66f_mono_neg (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : Monomial A) : Monomial (-A) := by
  obtain ⟨p, z, hz, hA⟩ := hA
  refine ⟨p, fun j => - z j, fun j => by simp [hz], fun i j => ?_⟩
  simp [hA]; split_ifs <;> simp

theorem g66f_mono_RX : Monomial pauliRX := by
  refine ⟨Equiv.swap 0 2 * Equiv.swap 1 3, ![1, -1, 1, -1], fun j => by fin_cases j <;> simp,
    fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [pauliRX, Equiv.swap_apply_def]

theorem g66f_mono_RZ : Monomial pauliRZ := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 2 3, fun _ => 1, fun j => by simp,
    fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [pauliRZ, Equiv.swap_apply_def]

theorem g66f_F1 : g66f_F false false false = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [g66f_F]
theorem g66f_FX : g66f_F false true false = pauliXFin := by
  rw [g66f_X]; ext i j; fin_cases i <;> fin_cases j <;> simp [g66f_F]
theorem g66f_FZ : g66f_F false false true = pauliZFin := by
  rw [g66f_Z]; ext i j; fin_cases i <;> fin_cases j <;> simp [g66f_F]
theorem g66f_Fneg : g66f_F true false false =
    pauliXFin * pauliZFin * (pauliXFin * pauliZFin) := by
  rw [← g66f_FX, ← g66f_FZ, g66f_Fmul, g66f_Fmul]; rfl
theorem g66f_Fdec (s x z : Bool) :
    g66f_F s x z = g66f_F s false false * (g66f_F false x false * g66f_F false false z) := by
  rw [g66f_Fmul, g66f_Fmul]; cases s <;> cases x <;> cases z <;> rfl

theorem g66f_mono_F (a b : ℂ) (hD : qubitCompletion a b * (qubitCompletion a b).conjTranspose = 1)
    (s x z : Bool) : Monomial (g66f_Rm a b (g66f_F s x z)) := by
  have hX := g66f_Rm_X a b hD
  have hZ := g66f_Rm_Z a b hD
  have h1 := g66f_Rm_one a b hD
  have hm := g66f_Rm_mul a b hD
  rw [g66f_Fdec, hm, hm]
  refine g66f_mono_mul _ _ ?_ (g66f_mono_mul _ _ ?_ ?_)
  · cases s
    · rw [g66f_F1, h1]; exact g66f_mono_one
    · rw [g66f_Fneg, hm, hm, hX, hZ]
      exact g66f_mono_mul _ _ (g66f_mono_mul _ _ g66f_mono_RX g66f_mono_RZ)
        (g66f_mono_mul _ _ g66f_mono_RX g66f_mono_RZ)
  · cases x
    · rw [g66f_F1, h1]; exact g66f_mono_one
    · rw [g66f_FX, hX]; exact g66f_mono_RX
  · cases z
    · rw [g66f_F1, h1]; exact g66f_mono_one
    · rw [g66f_FZ, hZ]; exact g66f_mono_RZ

theorem g66f_cover (u : Matrix.unitaryGroup (Fin 2) ℂ) (hu : u ∈ pauliLift) :
    ∃ s x z : Bool, (u : Matrix (Fin 2) (Fin 2) ℂ) = g66f_F s x z := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with h | h
    · exact ⟨false, true, false, by rw [h, g66f_FX]⟩
    · exact ⟨false, false, true, by rw [h, g66f_FZ]⟩
  | one => exact ⟨false, false, false, by rw [g66f_F1]; rfl⟩
  | mul u v _ _ hu hv =>
    obtain ⟨s, x, z, h1⟩ := hu
    obtain ⟨s', x', z', h2⟩ := hv
    refine ⟨xor s (xor s' (z && x')), xor x x', xor z z', ?_⟩
    rw [← g66f_Fmul, ← h1, ← h2]; rfl
  | inv u _ hu =>
    obtain ⟨s, x, z, h1⟩ := hu
    refine ⟨xor s (x && z), x, z, ?_⟩
    rw [← g66f_Fstar, ← h1]; rfl

def g66f_Xl : pauliLift :=
  ⟨⟨pauliXFin, by rw [Matrix.mem_unitaryGroup_iff, g66f_X]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Subgroup.subset_closure (Or.inl rfl)⟩
def g66f_Zl : pauliLift :=
  ⟨⟨pauliZFin, by rw [Matrix.mem_unitaryGroup_iff, g66f_Z]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Subgroup.subset_closure (Or.inr rfl)⟩

def g66f_f (t : Bool × Bool × Bool) : pauliLift :=
  (if t.1 then g66f_Xl * g66f_Zl * (g66f_Xl * g66f_Zl) else 1) * (if t.2.1 then g66f_Xl else 1) *
    (if t.2.2 then g66f_Zl else 1)

theorem g66f_coe_mul (g h : pauliLift) :
    (((g * h : pauliLift) : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((g : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((h : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
theorem g66f_coe_one :
    (((1 : pauliLift) : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl

theorem g66f_f_coe (s x z : Bool) :
    (((g66f_f (s, x, z) : pauliLift) : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      g66f_F s x z := by
  rw [g66f_Fdec s x z, ← Matrix.mul_assoc]
  unfold g66f_f
  simp only [g66f_coe_mul]
  congr 1; congr 1
  · cases s
    · exact g66f_F1.symm
    · exact (g66f_Fneg).symm
  · cases x
    · exact g66f_F1.symm
    · exact g66f_FX.symm
  · cases z
    · exact g66f_F1.symm
    · exact g66f_FZ.symm

theorem g66f_card : Nat.card pauliLift = 8 := by
  have hb : Function.Bijective g66f_f := by
    constructor
    · rintro ⟨s, x, z⟩ ⟨s', x', z'⟩ h
      have := congrArg (fun g : pauliLift =>
        ((g : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) h
      simp only [g66f_f_coe] at this
      obtain ⟨h1, h2, h3⟩ := g66f_Finj _ _ _ _ _ _ this
      subst h1 h2 h3; rfl
    · intro g
      obtain ⟨s, x, z, h⟩ := g66f_cover g.1 g.2
      exact ⟨(s, x, z), Subtype.ext (Subtype.ext (by rw [g66f_f_coe, h]))⟩
  rw [← Nat.card_eq_of_bijective g66f_f hb]
  simp
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem g66f_cov_of (A : Matrix (Fin 2) (Fin 2) ℂ) (Q : Matrix (Fin 2) (Fin 4) ℂ)
    (Rmat : Matrix (Fin 4) (Fin 4) ℂ) (h : A * Q = Q * Rmat) (hm : Monomial Rmat) (o : Fin 4) :
    ∃ q, A * columnEffect Q o * A.conjTranspose = columnEffect Q q := by
  obtain ⟨p, z, hz, hR⟩ := hm
  refine ⟨p o, ?_⟩
  have hcol : ∀ i, ∑ k, A i k * Q k o = Q i (p o) * z o := by
    intro i
    have := congrFun (congrFun h i) o
    simp only [Matrix.mul_apply] at this
    rw [this]; simp [hR, mul_ite, Finset.sum_ite_eq']
  have hzz : z o * conj (z o) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  ext i j
  simp only [Matrix.mul_apply, columnEffect, QAlgorithms.pureDensity, Matrix.of_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  have e1 : ∀ x, (∑ k, A i k * (Q k o * conj (Q x o))) = Q i (p o) * z o * conj (Q x o) := by
    intro x; rw [← hcol]; rw [Finset.sum_mul]; congr 1; funext k; ring
  simp_rw [e1]
  have e2 : (∑ x, Q i (p o) * z o * conj (Q x o) * conj (A j x)) =
      Q i (p o) * z o * conj (∑ x, A j x * Q x o) := by
    rw [map_sum, Finset.mul_sum]; congr 1; funext x; rw [map_mul]; ring
  rw [e2, hcol, map_mul]
  linear_combination (Q i (p o) * conj (Q j (p o))) * hzz

theorem solution (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    RankOnePOVM (qubitColumns a b) ∧
    EffectsCovariant pauliRepresentative (qubitColumns a b) ∧
    (pauliLift : Set (Matrix.unitaryGroup (Fin 2) ℂ)).Finite ∧ Nat.card pauliLift = 8 ∧
    pauliZFin * qubitColumns a b = qubitColumns a b * pauliRZ ∧
    pauliXFin * qubitColumns a b = qubitColumns a b * pauliRX ∧
    ∃ R : Rep pauliLift (Fin 4), UnitaryRep R ∧ (∀ g, Monomial (R g)) ∧
      MatrixIntertwines (naturalAction pauliLift) R (qubitColumns a b) ∧
      (∀ g, naturalAction pauliLift g = pauliXFin → R g = pauliRX) ∧
      (∀ g, naturalAction pauliLift g = pauliZFin → R g = pauliRZ) := by
  have hD : qubitCompletion a b * (qubitCompletion a b).conjTranspose = 1 := by
    have := g66f_unit a b hnorm; rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  have ha : a * conj a = (Complex.normSq a : ℂ) := Complex.mul_conj a
  have hb : b * conj b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  have hR : Complex.normSq a + Complex.normSq b = 1 / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; exact hnorm
  have hC : ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) = 1 / 2 := by
    rw [hR]; push_cast; ring
  push_cast at hC
  let R : Rep pauliLift (Fin 4) :=
    { toFun := fun g => g66f_Rm a b ((g : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      map_one' := g66f_Rm_one a b hD
      map_mul' := fun g h => g66f_Rm_mul a b hD _ _ }
  have hcard := g66f_card
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hcard, ?_, ?_, R, ?_, ?_, ?_, ?_, ?_⟩
  · intro o h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have hab : a = 0 ∧ b = 0 := by
      fin_cases o <;> simp [qubitColumns] at h0 h1 <;> exact ⟨by assumption, by assumption⟩
    rw [hab.1, hab.2] at hnorm; norm_num at hnorm
  · intro o
    have : columnEffect (qubitColumns a b) o =
        Matrix.vecMulVec (fun i => qubitColumns a b i o) (star (fun i => qubitColumns a b i o)) := by
      ext i j; rfl
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_four, columnEffect, QAlgorithms.pureDensity, qubitColumns] <;>
      linear_combination 2*ha + 2*hb + 2*hC
  · intro g o
    obtain ⟨g1, g2⟩ := g
    have hm : Monomial (g66f_Rm a b (pauliRepresentative (g1, g2))) := by
      have : pauliRepresentative (g1, g2) =
          g66f_F false false g2 * g66f_F false g1 false := by
        unfold pauliRepresentative
        cases g1 <;> cases g2 <;> simp [g66f_F1, g66f_FX, g66f_FZ]
      rw [this, g66f_Rm_mul a b hD]
      exact g66f_mono_mul _ _ (g66f_mono_F a b hD _ _ _) (g66f_mono_F a b hD _ _ _)
    exact g66f_cov_of _ _ _ (g66f_inter a b hD _) hm o
  · have : Finite pauliLift := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact Set.finite_coe_iff.mp this
  · rw [g66f_inter a b hD, g66f_Rm_Z a b hD]
  · rw [g66f_inter a b hD, g66f_Rm_X a b hD]
  · intro g; exact g66f_Rm_unit a b hD _ g.1.2
  · intro g
    obtain ⟨s, x, z, h⟩ := g66f_cover g.1 g.2
    show Monomial (g66f_Rm a b _)
    rw [h]; exact g66f_mono_F a b hD s x z
  · intro g; exact g66f_inter a b hD _
  · intro g hg
    show g66f_Rm a b _ = _
    rw [show ((g : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = pauliXFin from hg,
      g66f_Rm_X a b hD]
  · intro g hg
    show g66f_Rm a b _ = _
    rw [show ((g : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = pauliZFin from hg,
      g66f_Rm_Z a b hD]

end
