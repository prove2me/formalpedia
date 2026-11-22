-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.theorem_4_6_positivstellensatz
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:02:52.759029+00:00
-- url     : https://prove2.me/submissions/cf60a97b-ff83-4987-8200-614aa306b384

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone

open MvPolynomial SemialgebraicSDP.Psatz

namespace StenglePsatz

/-! ### Helper: LinearOrder and IsStrictOrderedRing from a positive cone on a field -/

@[instance_reducible]
noncomputable def linearOrderOfPosCone {F : Type*} [Field F] (P : Set F)
    (hadd : ∀ {a b}, a ∈ P → b ∈ P → a + b ∈ P)
    (htot : ∀ a, a ∈ P ∨ -a ∈ P)
    (hzero : ∀ {a}, a ∈ P → -a ∈ P → a = 0) :
    LinearOrder F := by
  classical
  have h0 : (0 : F) ∈ P := by
    rcases htot 0 with h | h
    · exact h
    · simpa using h
  refine
    { le := fun a b => b - a ∈ P
      lt := fun a b => b - a ∈ P ∧ a ≠ b
      le_refl := fun a => by simpa using h0
      le_trans := fun a b c hab hbc => by
        have : c - a = (c - b) + (b - a) := by ring
        rw [this]
        exact hadd hbc hab
      lt_iff_le_not_ge := fun a b => by
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun h3 => h2 ?_⟩
          have hneg : -(b - a) ∈ P := by simpa [neg_sub] using h3
          have heq : b - a = 0 := hzero h1 hneg
          exact (sub_eq_zero.mp heq).symm
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun h3 => h2 ?_⟩
          subst h3
          simpa using h0
      le_antisymm := fun a b hab hba => by
        have hneg : -(b - a) ∈ P := by simpa [neg_sub] using hba
        have heq : b - a = 0 := hzero hab hneg
        exact (sub_eq_zero.mp heq).symm
      le_total := fun a b => by
        rcases htot (b - a) with h | h
        · exact Or.inl h
        · exact Or.inr (by simpa [neg_sub] using h)
      toDecidableLE := Classical.decRel _ }

lemma isStrictOrderedRingOfPosCone {F : Type*} [Field F] (P : Set F)
    (hadd : ∀ {a b}, a ∈ P → b ∈ P → a + b ∈ P)
    (hmul : ∀ {a b}, a ∈ P → b ∈ P → a * b ∈ P)
    (htot : ∀ a, a ∈ P ∨ -a ∈ P)
    (hzero : ∀ {a}, a ∈ P → -a ∈ P → a = 0) :
    letI : LinearOrder F := linearOrderOfPosCone P hadd htot hzero
    IsStrictOrderedRing F := by
  let : LinearOrder F := linearOrderOfPosCone P hadd htot hzero
  have h1 : (1 : F) ∈ P := by
    rcases htot 1 with h | h
    · exact h
    · simpa using hmul h h
  have hlt_iff : ∀ a b : F, a < b ↔ b - a ∈ P ∧ a ≠ b := fun _ _ => Iff.rfl
  refine
    { add_le_add_left := fun a b hab c => by
        change (b + c) - (a + c) ∈ P
        have : (b + c) - (a + c) = b - a := by ring
        rw [this]
        exact hab
      le_of_add_le_add_left := fun a b c hab => by
        change c - b ∈ P
        have : c - b = (a + c) - (a + b) := by ring
        rw [this]
        exact hab
      zero_le_one := by
        change (1 : F) - 0 ∈ P
        simpa using h1
      mul_lt_mul_of_pos_left := fun a ha b c hbc => by
        rw [hlt_iff] at ha hbc ⊢
        refine ⟨?_, ?_⟩
        · have : a * c - a * b = a * (c - b) := by ring
          rw [this]
          exact hmul (by simpa using ha.1) hbc.1
        · intro heq
          apply hbc.2
          exact mul_left_cancel₀ ha.2.symm heq
      mul_lt_mul_of_pos_right := fun a ha b c hbc => by
        rw [hlt_iff] at ha hbc ⊢
        refine ⟨?_, ?_⟩
        · have : c * a - b * a = (c - b) * a := by ring
          rw [this]
          exact hmul hbc.1 (by simpa using ha.1)
        · intro heq
          apply hbc.2
          exact mul_right_cancel₀ ha.2.symm heq }

/-! ### Part A: Krivine–Stengle Algebraic Reduction to an Ordered Field Extension -/

structure IsGoodCone {n s t u : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ) (h : Fin u → MvPolynomial (Fin n) ℝ)
    (Q : Set (MvPolynomial (Fin n) ℝ)) : Prop where
  add_mem : ∀ {a b}, a ∈ Q → b ∈ Q → a + b ∈ Q
  mul_mem : ∀ {a b}, a ∈ Q → b ∈ Q → a * b ∈ Q
  sq_mem : ∀ a, a ^ 2 ∈ Q
  f_mem : ∀ j, f j ∈ Q
  ideal_sub : ∀ H ∈ Ideal.span (Set.range h), H ∈ Q
  neg_sq_notMem : ∀ G ∈ Submonoid.closure (Set.range g), -(G ^ 2) ∉ Q

lemma exists_prime_cone {n s t u : ℕ}
    (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ)
    (h : Fin u → MvPolynomial (Fin n) ℝ)
    (hno : ¬ ∃ F ∈ cone (Set.range f), ∃ G ∈ Submonoid.closure (Set.range g),
      ∃ H ∈ Ideal.span (Set.range h), F + G ^ 2 + H = 0) :
    ∃ (Q : Set (MvPolynomial (Fin n) ℝ)) (𝔭 : Ideal (MvPolynomial (Fin n) ℝ)),
      IsGoodCone f g h Q ∧
      (∀ a, a ∈ Q ∨ -a ∈ Q) ∧
      (∀ a, a ∈ 𝔭 ↔ a ∈ Q ∧ -a ∈ Q) ∧
      𝔭.IsPrime := by
  let R := MvPolynomial (Fin n) ℝ
  let I : Ideal R := Ideal.span (Set.range h)
  let M : Submonoid R := Submonoid.closure (Set.range g)
  let Q0 : Set R := {x | ∃ F ∈ cone (Set.range f), ∃ H ∈ I, x = F + H}
  have hQ0 : IsGoodCone f g h Q0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro a b ⟨F1, hF1, H1, hH1, rfl⟩ ⟨F2, hF2, H2, hH2, rfl⟩
      exact ⟨F1 + F2, InCone.add hF1 hF2, H1 + H2, I.add_mem hH1 hH2, by ring⟩
    · rintro a b ⟨F1, hF1, H1, hH1, rfl⟩ ⟨F2, hF2, H2, hH2, rfl⟩
      refine ⟨F1 * F2, InCone.mul hF1 hF2, F1 * H2 + H1 * F2 + H1 * H2, ?_, by ring⟩
      exact I.add_mem (I.add_mem (I.mul_mem_left F1 hH2) (I.mul_mem_right F2 hH1))
        (I.mul_mem_left H1 hH2)
    · intro a; exact ⟨a ^ 2, InCone.sq a, 0, I.zero_mem, by ring⟩
    · intro j; exact ⟨f j, InCone.of_mem ⟨j, rfl⟩, 0, I.zero_mem, by ring⟩
    · intro H hH; exact ⟨0 ^ 2, InCone.sq 0, H, hH, by ring⟩
    · rintro G hG ⟨F, hF, H, hH, heq⟩
      exact hno ⟨F, hF, G, hG, H, hH, by linear_combination -heq⟩
  have hzorn : ∃ Q, Q0 ⊆ Q ∧ Maximal (fun Q => Q ∈ {Q | IsGoodCone f g h Q}) Q := by
    apply zorn_subset_nonempty {Q | IsGoodCone f g h Q}
    · intro c hc hchain hne
      obtain ⟨Q1, hQ1⟩ := hne
      refine ⟨⋃₀ c, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun Q hQ => Set.subset_sUnion_of_mem hQ⟩
      · rintro a b ⟨Qa, hQa, ha⟩ ⟨Qb, hQb, hb⟩
        rcases hchain.total hQa hQb with hsub | hsub
        · exact ⟨Qb, hQb, (hc hQb).add_mem (hsub ha) hb⟩
        · exact ⟨Qa, hQa, (hc hQa).add_mem ha (hsub hb)⟩
      · rintro a b ⟨Qa, hQa, ha⟩ ⟨Qb, hQb, hb⟩
        rcases hchain.total hQa hQb with hsub | hsub
        · exact ⟨Qb, hQb, (hc hQb).mul_mem (hsub ha) hb⟩
        · exact ⟨Qa, hQa, (hc hQa).mul_mem ha (hsub hb)⟩
      · intro a; exact ⟨Q1, hQ1, (hc hQ1).sq_mem a⟩
      · intro j; exact ⟨Q1, hQ1, (hc hQ1).f_mem j⟩
      · intro H hH; exact ⟨Q1, hQ1, (hc hQ1).ideal_sub H hH⟩
      · rintro G hG ⟨Qa, hQa, hmem⟩; exact (hc hQa).neg_sq_notMem G hG hmem
    · exact hQ0
  obtain ⟨Q, _, hQmax⟩ := hzorn
  have hQ : IsGoodCone f g h Q := hQmax.prop
  have h0Q : (0 : R) ∈ Q := by simpa using hQ.sq_mem 0
  have h1Q : (1 : R) ∈ Q := by simpa using hQ.sq_mem 1
  have hsmul_supp : ∀ (x a : R), a ∈ Q → -a ∈ Q → x * a ∈ Q ∧ -(x * a) ∈ Q := by
    intro x a ha hna
    have h12 : (C (1 / 2 : ℝ) : R) * (C (1 / 2 : ℝ) : R) * (4 : R) = 1 := by
      have h4 : (4 : R) = C (4 : ℝ) := (map_ofNat C 4).symm
      rw [h4, ← C_mul, ← C_mul]
      norm_num
    have hid : ((x + 1) * C (1 / 2 : ℝ)) ^ 2 - ((x - 1) * C (1 / 2 : ℝ)) ^ 2 = x := by
      calc ((x + 1) * C (1 / 2 : ℝ)) ^ 2 - ((x - 1) * C (1 / 2 : ℝ)) ^ 2
          = x * (C (1 / 2 : ℝ) * C (1 / 2 : ℝ) * 4) := by ring
        _ = x * 1 := by rw [h12]
        _ = x := mul_one x
    constructor
    · have : x * a = ((x + 1) * C (1 / 2 : ℝ)) ^ 2 * a + ((x - 1) * C (1 / 2 : ℝ)) ^ 2 * (-a) := by
        conv_lhs => rw [← hid]
        ring
      rw [this]
      exact hQ.add_mem (hQ.mul_mem (hQ.sq_mem _) ha) (hQ.mul_mem (hQ.sq_mem _) hna)
    · have : -(x * a) = ((x + 1) * C (1 / 2 : ℝ)) ^ 2 * (-a) + ((x - 1) * C (1 / 2 : ℝ)) ^ 2 * a := by
        conv_lhs => rw [← hid]
        ring
      rw [this]
      exact hQ.add_mem (hQ.mul_mem (hQ.sq_mem _) hna) (hQ.mul_mem (hQ.sq_mem _) ha)
  let 𝔭 : Ideal R :=
    { carrier := {x | x ∈ Q ∧ -x ∈ Q}
      add_mem' := fun {a b} ha hb =>
        ⟨hQ.add_mem ha.1 hb.1, by rw [neg_add]; exact hQ.add_mem ha.2 hb.2⟩
      zero_mem' := ⟨h0Q, by simpa using h0Q⟩
      smul_mem' := fun x {a} ha => hsmul_supp x a ha.1 ha.2 }
  have hex_neg_sq : ∀ a : R, a ∉ Q →
      ∃ G ∈ M, ∃ s ∈ Q, ∃ t ∈ Q, -(G ^ 2) = s + a * t := by
    intro a ha
    let Q' : Set R := {x | ∃ s ∈ Q, ∃ t ∈ Q, x = s + a * t}
    have hsub : Q ⊆ Q' := fun x hx => ⟨x, hx, 0, h0Q, by ring⟩
    have ha' : a ∈ Q' := ⟨0, h0Q, 1, h1Q, by ring⟩
    by_contra hnone
    push Not at hnone
    have hQ' : IsGoodCone f g h Q' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rintro _ _ ⟨s1, hs1, t1, ht1, rfl⟩ ⟨s2, hs2, t2, ht2, rfl⟩
        exact ⟨s1 + s2, hQ.add_mem hs1 hs2, t1 + t2, hQ.add_mem ht1 ht2, by ring⟩
      · rintro _ _ ⟨s1, hs1, t1, ht1, rfl⟩ ⟨s2, hs2, t2, ht2, rfl⟩
        exact ⟨s1 * s2 + a ^ 2 * (t1 * t2),
          hQ.add_mem (hQ.mul_mem hs1 hs2) (hQ.mul_mem (hQ.sq_mem a) (hQ.mul_mem ht1 ht2)),
          s1 * t2 + t1 * s2, hQ.add_mem (hQ.mul_mem hs1 ht2) (hQ.mul_mem ht1 hs2), by ring⟩
      · intro x; exact hsub (hQ.sq_mem x)
      · intro j; exact hsub (hQ.f_mem j)
      · intro H hH; exact hsub (hQ.ideal_sub H hH)
      · rintro G hG ⟨s, hs, t, ht, heq⟩; exact hnone G hG s hs t ht heq
    exact ha ((hQmax.le_of_ge hQ' hsub) ha')
  have htotQ : ∀ a : R, a ∈ Q ∨ -a ∈ Q := by
    intro a
    by_contra hboth
    push Not at hboth
    obtain ⟨G1, hG1, s1, hs1, t1, ht1, heq1⟩ := hex_neg_sq a hboth.1
    obtain ⟨G2, hG2, s2, hs2, t2, ht2, heq2⟩ := hex_neg_sq (-a) hboth.2
    have hneg_t1 : -(G2 ^ 2 * t1) ∈ Q := by
      have hid : -(G2 ^ 2 * t1) = G1 ^ 2 * t2 + s1 * t2 + s2 * t1 := by
        linear_combination t2 * heq1 + t1 * heq2
      rw [hid]
      exact hQ.add_mem (hQ.add_mem (hQ.mul_mem (hQ.sq_mem G1) ht2) (hQ.mul_mem hs1 ht2))
        (hQ.mul_mem hs2 ht1)
    have hsupp_t1 : G2 ^ 2 * t1 ∈ 𝔭 := ⟨hQ.mul_mem (hQ.sq_mem G2) ht1, hneg_t1⟩
    have hat1 : a * (G2 ^ 2 * t1) ∈ Q := (𝔭.mul_mem_left a hsupp_t1).1
    have hcontra : -((G1 * G2) ^ 2) ∈ Q := by
      have hid : -((G1 * G2) ^ 2) = G2 ^ 2 * s1 + a * (G2 ^ 2 * t1) := by
        linear_combination G2 ^ 2 * heq1
      rw [hid]
      exact hQ.add_mem (hQ.mul_mem (hQ.sq_mem G2) hs1) hat1
    exact hQ.neg_sq_notMem (G1 * G2) (M.mul_mem hG1 hG2) hcontra
  have hprime : 𝔭.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1mem : (1 : R) ∈ 𝔭 := htop ▸ Submodule.mem_top
      exact hQ.neg_sq_notMem 1 M.one_mem (by simpa using h1mem.2)
    · intro x y hxy
      by_contra hneither
      push Not at hneither
      have hx_wlog : ∃ x' : R, x' ∈ Q ∧ -x' ∉ Q ∧ (x' = x ∨ x' = -x) := by
        rcases htotQ x with hx | hnx
        · exact ⟨x, hx, fun h => hneither.1 ⟨hx, h⟩, Or.inl rfl⟩
        · exact ⟨-x, hnx, fun h => hneither.1 ⟨neg_neg x ▸ h, hnx⟩, Or.inr rfl⟩
      have hy_wlog : ∃ y' : R, y' ∈ Q ∧ -y' ∉ Q ∧ (y' = y ∨ y' = -y) := by
        rcases htotQ y with hy | hny
        · exact ⟨y, hy, fun h => hneither.2 ⟨hy, h⟩, Or.inl rfl⟩
        · exact ⟨-y, hny, fun h => hneither.2 ⟨neg_neg y ▸ h, hny⟩, Or.inr rfl⟩
      obtain ⟨x', _, hnx', hxeq⟩ := hx_wlog
      obtain ⟨y', _, hny', hyeq⟩ := hy_wlog
      have hx'y' : x' * y' ∈ 𝔭 := by
        rcases hxeq with rfl | rfl <;> rcases hyeq with rfl | rfl
        · exact hxy
        · rw [mul_neg]; exact 𝔭.neg_mem hxy
        · rw [neg_mul]; exact 𝔭.neg_mem hxy
        · rw [neg_mul_neg]; exact hxy
      obtain ⟨G1, hG1, s1, hs1, t1, ht1, heq1⟩ := hex_neg_sq (-x') hnx'
      obtain ⟨G2, hG2, s2, hs2, t2, ht2, heq2⟩ := hex_neg_sq (-y') hny'
      have hneg_prod : -(x' * y' * (t1 * t2)) ∈ Q := (𝔭.mul_mem_right (t1 * t2) hx'y').2
      have hcontra : -((G1 * G2) ^ 2) ∈ Q := by
        have hid : -((G1 * G2) ^ 2) =
            G1 ^ 2 * s2 + G2 ^ 2 * s1 + s1 * s2 + -(x' * y' * (t1 * t2)) := by
          have e1 : x' * t1 = G1 ^ 2 + s1 := by linear_combination heq1
          have e2 : y' * t2 = G2 ^ 2 + s2 := by linear_combination heq2
          linear_combination (G2 ^ 2 + s2) * e1 + (x' * t1) * e2
        rw [hid]
        exact hQ.add_mem (hQ.add_mem (hQ.add_mem
          (hQ.mul_mem (hQ.sq_mem G1) hs2) (hQ.mul_mem (hQ.sq_mem G2) hs1))
          (hQ.mul_mem hs1 hs2)) hneg_prod
      exact hQ.neg_sq_notMem (G1 * G2) (M.mul_mem hG1 hG2) hcontra
  exact ⟨Q, 𝔭, hQ, htotQ, fun _ => Iff.rfl, hprime⟩

lemma ordered_field_of_prime_cone {R : Type} [CommRing R]
    (Q : Set R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hadd : ∀ {a b}, a ∈ Q → b ∈ Q → a + b ∈ Q)
    (hmul : ∀ {a b}, a ∈ Q → b ∈ Q → a * b ∈ Q)
    (htot : ∀ a, a ∈ Q ∨ -a ∈ Q)
    (hsupp : ∀ a, a ∈ 𝔭 ↔ a ∈ Q ∧ -a ∈ Q) :
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (φ : R →+* K),
      (∀ r : R, 0 ≤ φ r ↔ r ∈ Q) ∧ (∀ r : R, φ r = 0 ↔ r ∈ 𝔭) := by
  let D := R ⧸ 𝔭
  let K := FractionRing D
  let mk : R →+* D := Ideal.Quotient.mk 𝔭
  have h0Q : (0 : R) ∈ Q := ((hsupp 0).mp 𝔭.zero_mem).1
  let PD : Set D := mk '' Q
  have hmk_mem : ∀ r : R, mk r ∈ PD ↔ r ∈ Q := by
    intro r
    constructor
    · rintro ⟨r', hr', heq⟩
      have hdiff : r - r' ∈ 𝔭 := Ideal.Quotient.eq.mp heq.symm
      have : r = r' + (r - r') := by ring
      rw [this]
      exact hadd hr' ((hsupp _).mp hdiff).1
    · intro hr; exact ⟨r, hr, rfl⟩
  have hPD_add : ∀ {a b : D}, a ∈ PD → b ∈ PD → a + b ∈ PD := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, hadd ha hb, map_add mk a b⟩
  have hPD_mul : ∀ {a b : D}, a ∈ PD → b ∈ PD → a * b ∈ PD := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a * b, hmul ha hb, map_mul mk a b⟩
  have hPD_tot : ∀ a : D, a ∈ PD ∨ -a ∈ PD := by
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rcases htot r with h | h
    · exact Or.inl ⟨r, h, rfl⟩
    · exact Or.inr ⟨-r, h, map_neg mk r⟩
  have hPD_sq : ∀ a : D, a * a ∈ PD := by
    intro a
    rcases hPD_tot a with h | h
    · exact hPD_mul h h
    · exact neg_mul_neg a a ▸ hPD_mul h h
  have hPD_zero : ∀ {a : D}, a ∈ PD → -a ∈ PD → a = 0 := by
    intro a ha hna
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hmk_mem] at ha
    rw [← map_neg, hmk_mem] at hna
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hsupp r).mpr ⟨ha, hna⟩)
  have hPD_sq_cancel : ∀ {x d : D}, d ≠ 0 → x * (d * d) ∈ PD → x ∈ PD := by
    intro x d hd hxd
    rcases hPD_tot x with hx | hnx
    · exact hx
    · have hneg : -(x * (d * d)) ∈ PD := by
        have : -(x * (d * d)) = (-x) * (d * d) := by ring
        rw [this]; exact hPD_mul hnx (hPD_sq d)
      have h0 : x * (d * d) = 0 := hPD_zero hxd hneg
      have hx0 : x = 0 := (mul_eq_zero.mp h0).resolve_right (mul_ne_zero hd hd)
      subst hx0; exact ⟨0, h0Q, map_zero mk⟩
  let PK : Set K :=
    {z | ∃ a b : D, b ≠ 0 ∧ z = algebraMap D K a / algebraMap D K b ∧ a * b ∈ PD}
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  have hPK_iff : ∀ (a b : D) (hb : b ≠ 0),
      algebraMap D K a / algebraMap D K b ∈ PK ↔ a * b ∈ PD := by
    intro a b hb
    constructor
    · rintro ⟨a', b', hb', heq, ha'b'⟩
      have hbd : algebraMap D K b ≠ 0 := fun h => hb (hinj (by simpa using h))
      have hb'd : algebraMap D K b' ≠ 0 := fun h => hb' (hinj (by simpa using h))
      have hcross_K : algebraMap D K (a * b') = algebraMap D K (a' * b) := by
        rw [map_mul, map_mul]
        exact (div_eq_div_iff hbd hb'd).mp heq
      have hcross : a * b' = a' * b := hinj hcross_K
      have hmul_eq : (a * b) * (b' * b') = (a' * b') * (b * b) := by
        linear_combination (b * b') * hcross
      exact hPD_sq_cancel hb' (hmul_eq ▸ hPD_mul ha'b' (hPD_sq b))
    · intro hab; exact ⟨a, b, hb, rfl, hab⟩
  have hPK_add : ∀ {x y : K}, x ∈ PK → y ∈ PK → x + y ∈ PK := by
    rintro _ _ ⟨a1, b1, hb1, rfl, h1⟩ ⟨a2, b2, hb2, rfl, h2⟩
    have hb1K : algebraMap D K b1 ≠ 0 := fun h => hb1 (hinj (by simpa using h))
    have hb2K : algebraMap D K b2 ≠ 0 := fun h => hb2 (hinj (by simpa using h))
    refine ⟨a1 * b2 + a2 * b1, b1 * b2, mul_ne_zero hb1 hb2, ?_, ?_⟩
    · rw [div_add_div _ _ hb1K hb2K, map_add, map_mul, map_mul, map_mul]; ring
    · have hid : (a1 * b2 + a2 * b1) * (b1 * b2) =
          (a1 * b1) * (b2 * b2) + (a2 * b2) * (b1 * b1) := by ring
      rw [hid]
      exact hPD_add (hPD_mul h1 (hPD_sq b2)) (hPD_mul h2 (hPD_sq b1))
  have hPK_mul : ∀ {x y : K}, x ∈ PK → y ∈ PK → x * y ∈ PK := by
    rintro _ _ ⟨a1, b1, hb1, rfl, h1⟩ ⟨a2, b2, hb2, rfl, h2⟩
    refine ⟨a1 * a2, b1 * b2, mul_ne_zero hb1 hb2, ?_, ?_⟩
    · rw [map_mul, map_mul, div_mul_div_comm]
    · have : a1 * a2 * (b1 * b2) = (a1 * b1) * (a2 * b2) := by ring
      rw [this]; exact hPD_mul h1 h2
  have hPK_tot : ∀ z : K, z ∈ PK ∨ -z ∈ PK := by
    intro z
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors D) z
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hbK : algebraMap D K b ≠ 0 := fun h => hb0 (hinj (by simpa using h))
    have hz' : z = algebraMap D K a / algebraMap D K b := eq_div_of_mul_eq hbK hab
    rcases hPD_tot (a * b) with hab' | hnab
    · exact Or.inl ⟨a, b, hb0, hz', hab'⟩
    · refine Or.inr ⟨-a, b, hb0, ?_, (neg_mul a b).symm ▸ hnab⟩
      rw [hz', map_neg, neg_div]
  have hPK_zero : ∀ {z : K}, z ∈ PK → -z ∈ PK → z = 0 := by
    rintro _ ⟨a, b, hb, rfl, hab⟩ hnz
    have hneg_eq : -(algebraMap D K a / algebraMap D K b) =
        algebraMap D K (-a) / algebraMap D K b := by rw [map_neg, neg_div]
    rw [hneg_eq, hPK_iff (-a) b hb] at hnz
    have h0 : a * b = 0 := hPD_zero hab (neg_mul a b ▸ hnz)
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_right hb
    subst ha0; simp
  let : LinearOrder K := linearOrderOfPosCone PK hPK_add hPK_tot hPK_zero
  have : IsStrictOrderedRing K := isStrictOrderedRingOfPosCone PK hPK_add hPK_mul hPK_tot hPK_zero
  let φ : R →+* K := (algebraMap D K).comp mk
  refine ⟨K, inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · intro r
    change φ r - 0 ∈ PK ↔ r ∈ Q
    rw [sub_zero]
    have hdiv : φ r = algebraMap D K (mk r) / algebraMap D K 1 := by simp [φ]
    rw [hdiv, hPK_iff (mk r) 1 one_ne_zero, mul_one, hmk_mem]
  · intro r
    change algebraMap D K (mk r) = 0 ↔ r ∈ 𝔭
    rw [← map_zero (algebraMap D K), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

lemma exists_ordered_field_solution {n s t u : ℕ}
    (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ)
    (h : Fin u → MvPolynomial (Fin n) ℝ)
    (hno : ¬ ∃ F ∈ cone (Set.range f), ∃ G ∈ Submonoid.closure (Set.range g),
      ∃ H ∈ Ideal.span (Set.range h), F + G ^ 2 + H = 0) :
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (ι : ℝ →+* K) (x : Fin n → K),
      (∀ j, 0 ≤ MvPolynomial.eval₂ ι x (f j)) ∧
      (∀ k, MvPolynomial.eval₂ ι x (g k) ≠ 0) ∧
      (∀ l, MvPolynomial.eval₂ ι x (h l) = 0) := by
  obtain ⟨Q, 𝔭, hQ, htotQ, hsupp, hprime⟩ := exists_prime_cone f g h hno
  let : 𝔭.IsPrime := hprime
  obtain ⟨K, _, _, _, φ, hφ_nn, hφ_zero⟩ :=
    ordered_field_of_prime_cone Q 𝔭 hQ.add_mem hQ.mul_mem htotQ hsupp
  let ι : ℝ →+* K := φ.comp MvPolynomial.C
  let x : Fin n → K := fun i => φ (MvPolynomial.X i)
  have heval : ∀ p : MvPolynomial (Fin n) ℝ, MvPolynomial.eval₂ ι x p = φ p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [ι]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp => simp [map_mul, hp, x]
  refine ⟨K, inferInstance, inferInstance, inferInstance, ι, x, ?_, ?_, ?_⟩
  · intro j; rw [heval, hφ_nn]; exact hQ.f_mem j
  · intro k hgk
    rw [heval, hφ_zero] at hgk
    have hsq : -((g k) ^ 2) ∈ Q := by
      have hm : (g k) ^ 2 ∈ 𝔭 := by rw [sq]; exact 𝔭.mul_mem_left (g k) hgk
      exact ((hsupp _).mp hm).2
    exact hQ.neg_sq_notMem (g k) (Submonoid.subset_closure ⟨k, rfl⟩) hsq
  · intro l
    rw [heval, hφ_zero, hsupp]
    have hlI : h l ∈ Ideal.span (Set.range h) := Ideal.subset_span ⟨l, rfl⟩
    exact ⟨hQ.ideal_sub (h l) hlI, hQ.ideal_sub (-h l) ((Ideal.span (Set.range h)).neg_mem hlI)⟩

/-! ### Part B: Real Closure and Polynomial IVT -/

class HasPolyIVT (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  ivt : ∀ (p : Polynomial R) (a b : R), a < b → p.eval a < 0 → 0 < p.eval b →
    ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0

instance : HasPolyIVT ℝ where
  ivt p a b hab ha hb := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := ⟨ha, hb⟩
    have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
    obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo (le_of_lt hab) hcont h0
    exact ⟨c, hc.1, hc.2, hce⟩

/-- Extending any proper preordering of a field to a total ordering. -/
lemma exists_total_ordering_of_preordering {F : Type*} [Field F] (T : Set F)
    (hadd : ∀ {a b}, a ∈ T → b ∈ T → a + b ∈ T)
    (hmul : ∀ {a b}, a ∈ T → b ∈ T → a * b ∈ T)
    (hsq : ∀ a, a ^ 2 ∈ T)
    (hneg1 : (-1 : F) ∉ T) :
    ∃ P : Set F, T ⊆ P ∧
      (∀ {a b}, a ∈ P → b ∈ P → a + b ∈ P) ∧
      (∀ {a b}, a ∈ P → b ∈ P → a * b ∈ P) ∧
      (∀ a, a ∈ P ∨ -a ∈ P) ∧
      (-1 : F) ∉ P := by
  let IsPre (P : Set F) : Prop :=
    (∀ {a b}, a ∈ P → b ∈ P → a + b ∈ P) ∧
    (∀ {a b}, a ∈ P → b ∈ P → a * b ∈ P) ∧
    (∀ a, a ^ 2 ∈ P) ∧ (-1 : F) ∉ P
  have hzorn : ∃ P, T ⊆ P ∧ Maximal (fun P => P ∈ {P | IsPre P}) P := by
    apply zorn_subset_nonempty {P | IsPre P}
    · intro c hc hchain hne
      obtain ⟨P1, hP1⟩ := hne
      refine ⟨⋃₀ c, ⟨?_, ?_, ?_, ?_⟩, fun P hP => Set.subset_sUnion_of_mem hP⟩
      · rintro a b ⟨Pa, hPa, ha⟩ ⟨Pb, hPb, hb⟩
        rcases hchain.total hPa hPb with hsub | hsub
        · exact ⟨Pb, hPb, (hc hPb).1 (hsub ha) hb⟩
        · exact ⟨Pa, hPa, (hc hPa).1 ha (hsub hb)⟩
      · rintro a b ⟨Pa, hPa, ha⟩ ⟨Pb, hPb, hb⟩
        rcases hchain.total hPa hPb with hsub | hsub
        · exact ⟨Pb, hPb, (hc hPb).2.1 (hsub ha) hb⟩
        · exact ⟨Pa, hPa, (hc hPa).2.1 ha (hsub hb)⟩
      · intro a; exact ⟨P1, hP1, (hc hP1).2.2.1 a⟩
      · rintro ⟨Pa, hPa, hmem⟩; exact (hc hPa).2.2.2 hmem
    · exact ⟨hadd, hmul, hsq, hneg1⟩
  obtain ⟨P, hTP, hPmax⟩ := hzorn
  have hP : IsPre P := hPmax.prop
  have h0P : (0 : F) ∈ P := by simpa using hP.2.2.1 0
  have h1P : (1 : F) ∈ P := by simpa using hP.2.2.1 1
  have htot : ∀ a : F, a ∈ P ∨ -a ∈ P := by
    intro a
    by_contra hboth
    push Not at hboth
    have hex : ∀ x : F, x ∉ P → ∃ s ∈ P, ∃ t ∈ P, -1 = s + x * t := by
      intro x hx
      let P' : Set F := {y | ∃ s ∈ P, ∃ t ∈ P, y = s + x * t}
      have hsub : P ⊆ P' := fun y hy => ⟨y, hy, 0, h0P, by ring⟩
      have hx' : x ∈ P' := ⟨0, h0P, 1, h1P, by ring⟩
      by_contra hno
      push Not at hno
      have hP' : IsPre P' := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rintro _ _ ⟨s1, hs1, t1, ht1, rfl⟩ ⟨s2, hs2, t2, ht2, rfl⟩
          exact ⟨s1 + s2, hP.1 hs1 hs2, t1 + t2, hP.1 ht1 ht2, by ring⟩
        · rintro _ _ ⟨s1, hs1, t1, ht1, rfl⟩ ⟨s2, hs2, t2, ht2, rfl⟩
          exact ⟨s1 * s2 + x ^ 2 * (t1 * t2),
            hP.1 (hP.2.1 hs1 hs2) (hP.2.1 (hP.2.2.1 x) (hP.2.1 ht1 ht2)),
            s1 * t2 + t1 * s2, hP.1 (hP.2.1 hs1 ht2) (hP.2.1 ht1 hs2), by ring⟩
        · intro y; exact hsub (hP.2.2.1 y)
        · rintro ⟨s, hs, t, ht, heq⟩; exact hno s hs t ht heq
      exact hx ((hPmax.le_of_ge hP' hsub) hx')
    obtain ⟨s1, hs1, t1, ht1, heq1⟩ := hex a hboth.1
    obtain ⟨s2, hs2, t2, ht2, heq2⟩ := hex (-a) hboth.2
    have hsum_neg : -(t1 + t2) ∈ P := by
      have hid : -(t1 + t2) = s1 * t2 + s2 * t1 := by linear_combination t2 * heq1 + t1 * heq2
      rw [hid]; exact hP.1 (hP.2.1 hs1 ht2) (hP.2.1 hs2 ht1)
    have ht1_ne : t1 ≠ 0 := by
      intro h0; subst h0; exact hP.2.2.2 ((by simpa using heq1 : -1 = s1) ▸ hs1)
    by_cases hsum0 : t1 + t2 = 0
    · have ht2eq : t2 = -t1 := by linear_combination hsum0
      have hcontra : (-1 : F) ∈ P := by
        have : (-1 : F) = (-t1) * t1 * (t1⁻¹) ^ 2 := by field_simp [ht1_ne]
        rw [this]; exact hP.2.1 (hP.2.1 (ht2eq ▸ ht2) ht1) (hP.2.2.1 t1⁻¹)
      exact hP.2.2.2 hcontra
    · have hcontra : (-1 : F) ∈ P := by
        have : (-1 : F) = (-(t1 + t2)) * (t1 + t2) * ((t1 + t2)⁻¹) ^ 2 := by field_simp [hsum0]
        rw [this]; exact hP.2.1 (hP.2.1 hsum_neg (hP.1 ht1 ht2)) (hP.2.2.1 (t1 + t2)⁻¹)
      exact hP.2.2.2 hcontra
  exact ⟨P, hTP, hP.1, hP.2.1, htot, hP.2.2.2⟩

/-- In a quadratic extension `C' = R(j)` with `j^2 = -1` over a field where nonnegative elements
have square roots, every element of `C'` is a square. -/
lemma adj_i_every_sq {R E : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field E] [Algebra R E] (j : E) (hj_sq : j ^ 2 = -1)
    (hsq : ∀ a : R, 0 ≤ a → ∃ r : R, r ^ 2 = a) :
    ∃ C' : IntermediateField R E,
      (∀ z, z ∈ C' ↔ ∃ a b : R, z = algebraMap R E a + algebraMap R E b * j) ∧
      (∀ z : C', ∃ w : C', w ^ 2 = z) := by
  let C' : IntermediateField R E :=
    { carrier := {z | ∃ a b : R, z = algebraMap R E a + algebraMap R E b * j}
      add_mem' := by
        rintro _ _ ⟨a1, b1, rfl⟩ ⟨a2, b2, rfl⟩
        exact ⟨a1 + a2, b1 + b2, by rw [map_add, map_add]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a1, b1, rfl⟩ ⟨a2, b2, rfl⟩
        refine ⟨a1 * a2 - b1 * b2, a1 * b2 + b1 * a2, ?_⟩
        rw [map_sub, map_add, map_mul, map_mul, map_mul, map_mul]
        linear_combination (algebraMap R E b1 * algebraMap R E b2) * hj_sq
      one_mem' := ⟨1, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        by_cases h0 : a = 0 ∧ b = 0
        · rcases h0 with ⟨rfl, rfl⟩; exact ⟨0, 0, by simp⟩
        · have hd : a ^ 2 + b ^ 2 ≠ 0 := by
            intro hsum; apply h0
            have ha0 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
            have hb0 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
            exact ⟨sq_eq_zero_iff.mp ha0, sq_eq_zero_iff.mp hb0⟩
          refine ⟨a / (a ^ 2 + b ^ 2), -b / (a ^ 2 + b ^ 2), ?_⟩
          have hdE : algebraMap R E (a ^ 2 + b ^ 2) ≠ 0 :=
            fun h => hd ((algebraMap R E).injective (by simpa using h))
          have hmul1 : (algebraMap R E a + algebraMap R E b * j) *
              (algebraMap R E (a / (a ^ 2 + b ^ 2)) +
                algebraMap R E (-b / (a ^ 2 + b ^ 2)) * j) = 1 := by
            rw [map_div₀, map_div₀, map_neg]
            have hnum : (algebraMap R E a + algebraMap R E b * j) *
                (algebraMap R E a + -(algebraMap R E b) * j) =
                algebraMap R E (a ^ 2 + b ^ 2) := by
              rw [map_add, map_pow, map_pow]
              linear_combination -(algebraMap R E b) ^ 2 * hj_sq
            calc (algebraMap R E a + algebraMap R E b * j) *
                  (algebraMap R E a / algebraMap R E (a ^ 2 + b ^ 2) +
                    -(algebraMap R E b) / algebraMap R E (a ^ 2 + b ^ 2) * j)
                = ((algebraMap R E a + algebraMap R E b * j) *
                    (algebraMap R E a + -(algebraMap R E b) * j)) /
                    algebraMap R E (a ^ 2 + b ^ 2) := by ring
              _ = algebraMap R E (a ^ 2 + b ^ 2) / algebraMap R E (a ^ 2 + b ^ 2) := by rw [hnum]
              _ = 1 := div_self hdE
          exact inv_eq_of_mul_eq_one_right hmul1
      algebraMap_mem' := fun a => ⟨a, 0, by simp⟩ }
  refine ⟨C', fun _ => Iff.rfl, ?_⟩
  intro ⟨z, a, b, hz⟩
  obtain ⟨r0, hr0⟩ := hsq (a ^ 2 + b ^ 2) (by positivity)
  let r := if 0 ≤ r0 then r0 else -r0
  have hr_nonneg : 0 ≤ r := by dsimp [r]; split_ifs with h <;> linarith
  have hr_sq : r ^ 2 = a ^ 2 + b ^ 2 := by dsimp [r]; split_ifs <;> linear_combination hr0
  have hru_le : |a| ≤ r := by
    have : |a| ^ 2 ≤ r ^ 2 := by rw [sq_abs, hr_sq]; nlinarith [sq_nonneg b]
    nlinarith [abs_nonneg a]
  obtain ⟨u0, hu0⟩ := hsq ((r + a) / 2) (by linarith [neg_le_of_abs_le hru_le])
  obtain ⟨v0, hv0⟩ := hsq ((r - a) / 2) (by linarith [le_of_abs_le hru_le])
  let u := if 0 ≤ u0 then u0 else -u0
  let v1 := if 0 ≤ v0 then v0 else -v0
  have hu_nn : 0 ≤ u := by dsimp [u]; split_ifs with h <;> linarith
  have hv1_nn : 0 ≤ v1 := by dsimp [v1]; split_ifs with h <;> linarith
  have hu_sq : u ^ 2 = (r + a) / 2 := by dsimp [u]; split_ifs <;> linear_combination hu0
  have hv1_sq : v1 ^ 2 = (r - a) / 2 := by dsimp [v1]; split_ifs <;> linear_combination hv0
  have h2uv_sq : (2 * u * v1) ^ 2 = b ^ 2 := by
    calc (2 * u * v1) ^ 2 = 4 * u ^ 2 * v1 ^ 2 := by ring
      _ = 4 * ((r + a) / 2) * ((r - a) / 2) := by rw [hu_sq, hv1_sq]
      _ = r ^ 2 - a ^ 2 := by ring
      _ = b ^ 2 := by linear_combination hr_sq
  let v := if 0 ≤ b then v1 else -v1
  have hv_sq : v ^ 2 = (r - a) / 2 := by dsimp [v]; split_ifs <;> linear_combination hv1_sq
  have h2uv : 2 * u * v = b := by
    have habs : 2 * u * v1 = |b| := by
      have hnn : 0 ≤ 2 * u * v1 := by positivity
      have : (2 * u * v1) ^ 2 = |b| ^ 2 := by rw [sq_abs]; exact h2uv_sq
      nlinarith [abs_nonneg b]
    dsimp [v]; split_ifs with hb
    · rw [abs_of_nonneg hb] at habs; exact habs
    · rw [abs_of_neg (lt_of_not_ge hb)] at habs; linarith
  refine ⟨⟨algebraMap R E u + algebraMap R E v * j, u, v, rfl⟩, ?_⟩
  ext
  change (algebraMap R E u + algebraMap R E v * j) ^ 2 = z
  rw [hz]
  have h1 : u ^ 2 - v ^ 2 = a := by linear_combination hu_sq - hv_sq
  calc (algebraMap R E u + algebraMap R E v * j) ^ 2
      = algebraMap R E (u ^ 2 - v ^ 2) + algebraMap R E (2 * u * v) * j +
          (algebraMap R E v) ^ 2 * (j ^ 2 + 1) := by
        rw [map_sub, map_pow, map_pow, map_mul, map_mul, map_ofNat]; ring
    _ = algebraMap R E a + algebraMap R E b * j := by rw [h1, h2uv, hj_sq]; ring

/-- A field of characteristic ≠ 2 in which every element is a square has no quadratic extension. -/
lemma no_quad_of_every_sq {C E : Type} [Field C] [Field E] [Algebra C E]
    [FiniteDimensional C E] (h2ne : (2 : C) ≠ 0) (hsq : ∀ z : C, ∃ w : C, w ^ 2 = z)
    (M : IntermediateField C E) : Module.finrank C M ≠ 2 := by
  intro hfin
  obtain ⟨x, hxnot⟩ : ∃ x : M, x ∉ (⊥ : IntermediateField C M) := by
    by_contra hall
    push Not at hall
    have htop : (⊥ : IntermediateField C M) = ⊤ := eq_top_iff.mpr fun x _ => hall x
    have := congr_arg (fun K : IntermediateField C M => Module.finrank C K) htop
    simp only [IntermediateField.finrank_bot, IntermediateField.finrank_top'] at this
    omega
  have halg : IsIntegral C x := Algebra.IsIntegral.isIntegral x
  have hdeg_le : (minpoly C x).natDegree ≤ 2 := by
    have h1 := IntermediateField.adjoin.finrank halg
    have h2 : Module.finrank C (IntermediateField.adjoin C ({x} : Set M)) ≤ Module.finrank C M :=
      Submodule.finrank_le ((IntermediateField.adjoin C ({x} : Set M)).toSubmodule)
    omega
  have hdeg_gt1 : 1 < (minpoly C x).natDegree := by
    by_contra hle
    have hpos := minpoly.natDegree_pos halg
    have hdeg1 : (minpoly C x).natDegree = 1 := by omega
    have hfin1 : Module.finrank C (IntermediateField.adjoin C ({x} : Set M)) = 1 := by
      rw [IntermediateField.adjoin.finrank halg, hdeg1]
    have hle1 : (⊥ : IntermediateField C M).toSubmodule ≤
        (IntermediateField.adjoin C ({x} : Set M)).toSubmodule :=
      fun _ hy => (bot_le : (⊥ : IntermediateField C M) ≤ IntermediateField.adjoin C ({x} : Set M)) hy
    have heq : (⊥ : IntermediateField C M).toSubmodule =
        (IntermediateField.adjoin C ({x} : Set M)).toSubmodule :=
      Submodule.eq_of_le_of_finrank_eq hle1 (by simp [hfin1])
    exact hxnot ((SetLike.ext_iff.mp heq x).mpr (IntermediateField.mem_adjoin_simple_self C x))
  have hdeg2 : (minpoly C x).natDegree = 2 := by omega
  have hmon : (minpoly C x).Monic := minpoly.monic halg
  let b : C := (minpoly C x).coeff 1
  let c : C := (minpoly C x).coeff 0
  have hpoly_eq : minpoly C x = Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c := by
    ext k
    by_cases hk0 : k = 0
    · subst hk0; simp [c]
    by_cases hk1 : k = 1
    · subst hk1; simp [b]
    by_cases hk2 : k = 2
    · subst hk2
      have hlead : (minpoly C x).coeff 2 = 1 := hdeg2 ▸ hmon.leadingCoeff
      rw [hlead]; simp
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [Polynomial.coeff_X, Polynomial.coeff_C, hk0, Ne.symm hk1, hk2]
  have hroot : x ^ 2 + algebraMap C M b * x + algebraMap C M c = 0 := by
    have := minpoly.aeval C x
    rw [hpoly_eq] at this
    simpa using this
  obtain ⟨d, hd⟩ := hsq ((b / 2) ^ 2 - c)
  have hfact : (x + algebraMap C M (b / 2) - algebraMap C M d) *
      (x + algebraMap C M (b / 2) + algebraMap C M d) = 0 := by
    have hdM : (algebraMap C M d) ^ 2 = (algebraMap C M (b / 2)) ^ 2 - algebraMap C M c := by
      rw [← map_pow, hd, map_sub, map_pow]
    have hb2 : algebraMap C M b = 2 * algebraMap C M (b / 2) := by
      rw [← map_ofNat (algebraMap C M) 2, ← map_mul]
      congr 1; field_simp [h2ne]
    linear_combination hroot - hdM - x * hb2
  rcases mul_eq_zero.mp hfact with h1 | h2
  · have hx_eq : x = algebraMap C M (d - b / 2) := by rw [map_sub]; linear_combination h1
    exact hxnot (hx_eq ▸ IntermediateField.algebraMap_mem _ _)
  · have hx_eq : x = algebraMap C M (-d - b / 2) := by
      rw [map_sub, map_neg]; linear_combination h2
    exact hxnot (hx_eq ▸ IntermediateField.algebraMap_mem _ _)

/-- Over a real closed field, every monic irreducible polynomial has degree 1 or is `(X - u)^2 + v^2`. -/
lemma realClosed_irred_factor {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hsq : ∀ a : R, 0 ≤ a → ∃ r : R, r ^ 2 = a)
    (hodd : ∀ f : Polynomial R, Odd f.natDegree → ∃ r : R, f.eval r = 0)
    (q : Polynomial R) (hq_monic : q.Monic) (hq_irr : Irreducible q) :
    (∃ r : R, q = Polynomial.X - Polynomial.C r) ∨
    (∃ u v : R, v ≠ 0 ∧ q = (Polynomial.X - Polynomial.C u) ^ 2 + Polynomial.C (v ^ 2)) := by
  let p : Polynomial R := (Polynomial.X ^ 2 + 1) * q
  let E := p.SplittingField
  have : IsGalois R E := ⟨⟩
  have hp_splits : Polynomial.Splits (p.map (algebraMap R E)) := Polynomial.SplittingField.splits p
  have hX2_ne : (Polynomial.X ^ 2 + 1 : Polynomial R) ≠ 0 := by
    intro h0; have := congr_arg (Polynomial.eval (0 : R)) h0; simp at this
  have hp_map_ne : p.map (algebraMap R E) ≠ 0 :=
    Polynomial.map_ne_zero (mul_ne_zero hX2_ne hq_monic.ne_zero)
  have hX2_splits : Polynomial.Splits ((Polynomial.X ^ 2 + 1 : Polynomial R).map (algebraMap R E)) :=
    Polynomial.Splits.of_dvd hp_splits hp_map_ne
      (Polynomial.map_dvd (algebraMap R E) (dvd_mul_right _ _))
  have hX2_deg : ((Polynomial.X ^ 2 + 1 : Polynomial R).map (algebraMap R E)).natDegree = 2 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap R E).injective]; compute_degree!
  have hX2_roots_pos : 0 < ((Polynomial.X ^ 2 + 1 : Polynomial R).map (algebraMap R E)).roots.card := by
    rw [Polynomial.splits_iff_card_roots.mp hX2_splits, hX2_deg]; norm_num
  obtain ⟨j, hj_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hX2_roots_pos
  have hj_root : ((Polynomial.X ^ 2 + 1 : Polynomial R).map (algebraMap R E)).IsRoot j :=
    Polynomial.isRoot_of_mem_roots hj_mem
  have hj_sq : j ^ 2 = -1 := by
    have : j ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using hj_root
    linear_combination this
  have hj_notMem : ∀ a : R, algebraMap R E a ≠ j := by
    intro a ha
    have h1 : algebraMap R E (a ^ 2 + 1) = 0 := by
      rw [map_add, map_pow, map_one, ha, hj_sq]; ring
    have h2 : a ^ 2 + 1 = 0 := (algebraMap R E).injective (by simpa using h1)
    have h3 : (0 : R) < a ^ 2 + 1 := by positivity
    linarith
  obtain ⟨C', hC'_mem, hC'_sq⟩ := adj_i_every_sq j hj_sq hsq
  have h2C' : (2 : C') ≠ 0 := fun h2 => two_ne_zero (congr_arg Subtype.val h2 : (2 : E) = 0)
  -- Sylow 2-subgroup argument on Gal(E / R)
  let G := E ≃ₐ[R] E
  have : Finite G := Finite.of_fintype G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H⟩ := (inferInstance : Nonempty (Sylow 2 G))
  let F : IntermediateField R E := IntermediateField.fixedField H.toSubgroup
  have hcard_G : Nat.card G = Module.finrank R E := IsGalois.card_aut_eq_finrank R E
  have hfin_FE : Module.finrank F E = Nat.card H.toSubgroup :=
    IntermediateField.finrank_fixedField_eq_card H.toSubgroup
  have hmul_fin : Module.finrank R F * Module.finrank F E = Module.finrank R E :=
    Module.finrank_mul_finrank R F E
  have hmul_idx : Nat.card H.toSubgroup * H.toSubgroup.index = Nat.card G :=
    Subgroup.card_mul_index H.toSubgroup
  have hfin_RF : Module.finrank R F = H.toSubgroup.index := by
    have hpos : 0 < Nat.card H.toSubgroup := Nat.card_pos
    nlinarith
  have hodd_RF : Odd (Module.finrank R F) := by
    rw [hfin_RF]
    have hndvd := H.not_dvd_index
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R F
  have halgα : IsIntegral R α := Algebra.IsIntegral.isIntegral α
  have hdegα : (minpoly R α).natDegree = Module.finrank R F := by
    rw [← IntermediateField.adjoin.finrank halgα, hα, IntermediateField.finrank_top']
  obtain ⟨r0, hr0⟩ := hodd (minpoly R α) (hdegα ▸ hodd_RF)
  have hdegα1 : (minpoly R α).natDegree = 1 := by
    have hdvd : Polynomial.X - Polynomial.C r0 ∣ minpoly R α := Polynomial.dvd_iff_isRoot.mpr hr0
    have hnu : ¬ IsUnit (Polynomial.X - Polynomial.C r0) := by
      intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [Polynomial.natDegree_X_sub_C] at this; omega
    rcases (minpoly.irreducible halgα).dvd_iff.mp hdvd with h1 | h2
    · exact absurd h1 hnu
    · exact le_antisymm (by
        have := Polynomial.natDegree_le_of_dvd h2.dvd (Polynomial.X_sub_C_ne_zero r0)
        rw [Polynomial.natDegree_X_sub_C] at this; omega) (minpoly.natDegree_pos halgα)
  have hidx1 : H.toSubgroup.index = 1 := by omega
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp H.isPGroup'
  have hcard_G_pow : Nat.card G = 2 ^ m := by
    rw [← hm]; have : Nat.card H.toSubgroup * 1 = Nat.card G := hidx1 ▸ hmul_idx; linarith
  have : IsGalois C' E := IsGalois.tower_top_intermediateField C'
  let GC := E ≃ₐ[C'] E
  have : Finite GC := Finite.of_fintype GC
  have hcard_GC : Nat.card GC = Module.finrank C' E := IsGalois.card_aut_eq_finrank C' E
  have hdvd_GC : Nat.card GC ∣ 2 ^ m := by
    rw [hcard_GC, ← hcard_G_pow, hcard_G]
    exact ⟨Module.finrank R C', by rw [mul_comm]; exact (Module.finrank_mul_finrank R C' E).symm⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_iff_card_dvd_pow.mpr ⟨m, hdvd_GC⟩)
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkne
    obtain ⟨N, hNcard⟩ := Sylow.exists_subgroup_card_pow_prime 2
      (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 1) : 2 ^ (k - 1) ∣ Nat.card GC)
    let M : IntermediateField C' E := IntermediateField.fixedField N
    have hfin_ME : Module.finrank M E = 2 ^ (k - 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card N, hNcard]
    have hfin_CM : Module.finrank C' M = 2 := by
      have hprod := Module.finrank_mul_finrank C' M E
      rw [hfin_ME, ← hcard_GC, hk] at hprod
      have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hkpos, pow_succ']
      have hpos : 0 < 2 ^ (k - 1) := by positivity
      nlinarith
    exact no_quad_of_every_sq h2C' hC'_sq M hfin_CM
  have hfin_CE : Module.finrank C' E = 1 := by rw [← hcard_GC, hk, hk0]; simp
  have hC'_top : C' = ⊤ := by
    apply eq_top_iff.mpr; intro z _
    have hfin_eq : Module.finrank R C'.toSubmodule = Module.finrank R E := by
      have := Module.finrank_mul_finrank R C' E; rw [hfin_CE, mul_one] at this; exact this
    exact (SetLike.ext_iff.mp (Submodule.eq_top_of_finrank_eq hfin_eq) z).mpr trivial
  have hq_splits : Polynomial.Splits (q.map (algebraMap R E)) :=
    Polynomial.Splits.of_dvd hp_splits hp_map_ne
      (Polynomial.map_dvd (algebraMap R E) (dvd_mul_left _ _))
  have hq_deg_pos : 0 < q.natDegree := by
    by_contra h0
    have hq1 : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_monic (by omega)
    exact hq_irr.not_isUnit (hq1 ▸ isUnit_one)
  have hq_roots_pos : 0 < (q.map (algebraMap R E)).roots.card := by
    rw [Polynomial.splits_iff_card_roots.mp hq_splits,
      Polynomial.natDegree_map_eq_of_injective (algebraMap R E).injective]
    exact hq_deg_pos
  obtain ⟨z, hz_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hq_roots_pos
  have hz_root : (q.map (algebraMap R E)).IsRoot z := Polynomial.isRoot_of_mem_roots hz_mem
  obtain ⟨u, v, hz_eq⟩ := (hC'_mem z).mp (hC'_top ▸ trivial)
  by_cases hv : v = 0
  · subst hv
    have hu_root : q.eval u = 0 := by
      have h1 : Polynomial.eval (algebraMap R E u) (q.map (algebraMap R E)) = 0 := by
        simpa [hz_eq] using hz_root
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply] at h1
      exact (algebraMap R E).injective (by simpa using h1)
    have hdvd : Polynomial.X - Polynomial.C u ∣ q := Polynomial.dvd_iff_isRoot.mpr hu_root
    have hnu : ¬ IsUnit (Polynomial.X - Polynomial.C u) := by
      intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [Polynomial.natDegree_X_sub_C] at this; omega
    rcases hq_irr.dvd_iff.mp hdvd with h1 | h2
    · exact absurd h1 hnu
    · exact Or.inl ⟨u, Polynomial.eq_of_monic_of_associated hq_monic (Polynomial.monic_X_sub_C u) h2⟩
  · let g : Polynomial R := (Polynomial.X - Polynomial.C u) ^ 2 + Polynomial.C (v ^ 2)
    have hg_monic : g.Monic := by
      dsimp [g]
      refine ((Polynomial.monic_X_sub_C u).pow 2).add_of_left ?_
      calc (Polynomial.C (v ^ 2)).degree ≤ 0 := Polynomial.degree_C_le
        _ < 2 := by norm_num
        _ = ((Polynomial.X - Polynomial.C u) ^ 2 : Polynomial R).degree := by
          rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]; norm_num
    have hg_root : Polynomial.aeval z g = 0 := by
      dsimp [g]
      rw [map_add, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C,
        hz_eq, map_pow]
      calc (algebraMap R E u + algebraMap R E v * j - algebraMap R E u) ^ 2 +
            (algebraMap R E v) ^ 2
          = (algebraMap R E v) ^ 2 * (j ^ 2 + 1) := by ring
        _ = 0 := by rw [hj_sq]; ring
    have hq_min : q = minpoly R z := by
      have hq_aeval : Polynomial.aeval z q = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hz_root
      exact minpoly.eq_of_irreducible_of_monic hq_irr hq_aeval hq_monic
    have hq_dvd_g : q ∣ g := hq_min ▸ minpoly.dvd R z hg_root
    have hg_deg : g.natDegree = 2 := by dsimp [g]; compute_degree!
    have hq_ge2 : 2 ≤ q.natDegree := by
      by_contra hlt
      have hq1 : q.natDegree = 1 := by omega
      obtain ⟨r, hr⟩ : ∃ r : R, q = Polynomial.X - Polynomial.C r := by
        refine ⟨-q.coeff 0, ?_⟩
        ext k
        by_cases hk0 : k = 0
        · subst hk0; simp
        by_cases hk1 : k = 1
        · subst hk1
          have hlead : q.coeff 1 = 1 := hq1 ▸ hq_monic.leadingCoeff
          rw [hlead]; simp
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X, Polynomial.coeff_C, hk0, Ne.symm hk1]
      have hz_r : z = algebraMap R E r := by
        have : Polynomial.aeval z (Polynomial.X - Polynomial.C r) = 0 := by
          rw [← hr]; simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hz_root
        simpa [sub_eq_zero] using this
      have hv_ne : algebraMap R E v ≠ 0 :=
        fun h => hv ((algebraMap R E).injective (by simpa using h))
      have hj_in_R : j = algebraMap R E ((r - u) / v) := by
        rw [map_div₀, map_sub]
        apply eq_div_of_mul_eq hv_ne
        linear_combination -(hz_r.symm.trans hz_eq)
      exact hj_notMem ((r - u) / v) hj_in_R.symm
    have hq_le2 : q.natDegree ≤ 2 :=
      hg_deg ▸ Polynomial.natDegree_le_of_dvd hq_dvd_g hg_monic.ne_zero
    obtain ⟨w, hw⟩ := hq_dvd_g
    have hw_ne : w ≠ 0 := by rintro rfl; simp at hw; exact hg_monic.ne_zero hw
    have hw_deg : w.natDegree = 0 := by
      have hmul_deg := Polynomial.natDegree_mul hq_monic.ne_zero hw_ne
      rw [← hw] at hmul_deg
      omega
    have hw_mon : w.Monic := by
      have : (q * w).leadingCoeff = 1 := hw ▸ hg_monic.leadingCoeff
      rw [Polynomial.leadingCoeff_mul, hq_monic.leadingCoeff, one_mul] at this
      exact this
    have hw1 : w = 1 := Polynomial.eq_one_of_monic_natDegree_zero hw_mon hw_deg
    rw [hw1, mul_one] at hw
    exact Or.inr ⟨u, v, hv, hw.symm⟩

lemma hasPolyIVT_of_realClosed {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hsq : ∀ a : R, 0 ≤ a → ∃ r : R, r ^ 2 = a)
    (hodd : ∀ f : Polynomial R, Odd f.natDegree → ∃ r : R, f.eval r = 0) :
    HasPolyIVT R := by
  refine ⟨fun p a b hab ha hb => ?_⟩
  suffices ∀ d : ℕ, ∀ p : Polynomial R, p.natDegree ≤ d →
      ∀ a b : R, a < b → p.eval a * p.eval b < 0 → ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0 by
    exact this p.natDegree p le_rfl a b hab (mul_neg_of_neg_of_pos ha hb)
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hdeg a b hab hprod
    have hp_ne : p ≠ 0 := by rintro rfl; simp at hprod
    have hp_deg_pos : 0 < p.natDegree := by
      by_contra h0
      have hp0 : p.natDegree = 0 := by omega
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp0] at hprod
      simp only [Polynomial.eval_C] at hprod
      linarith [sq_nonneg (p.coeff 0)]
    let c := p.leadingCoeff
    have hc_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
    let q := Polynomial.C c⁻¹ * p
    have hq_mon : q.Monic := by
      dsimp [q]; rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hc_ne
    have hq_deg : q.natDegree = p.natDegree := by
      dsimp [q]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hc_ne)]
    have hq_prod : q.eval a * q.eval b < 0 := by
      dsimp [q]; simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have : c⁻¹ * p.eval a * (c⁻¹ * p.eval b) = (c⁻¹) ^ 2 * (p.eval a * p.eval b) := by ring
      rw [this]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (inv_ne_zero hc_ne)) hprod
    have hroot_of_q : ∀ x, q.eval x = 0 → p.eval x = 0 := by
      intro x hx; dsimp [q] at hx; simp only [Polynomial.eval_mul, Polynomial.eval_C] at hx
      exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero hc_ne)
    by_cases hq_irr : Irreducible q
    · rcases realClosed_irred_factor hsq hodd q hq_mon hq_irr with ⟨r, hqr⟩ | ⟨u, v, hv, hqr⟩
      · rw [hqr] at hq_prod
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hq_prod
        refine ⟨r, ?_, ?_, hroot_of_q r (by rw [hqr]; simp)⟩
        · by_contra hle; push Not at hle; nlinarith
        · by_contra hle; push Not at hle; nlinarith
      · rw [hqr] at hq_prod
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hq_prod
        have h1 : 0 < (a - u) ^ 2 + v ^ 2 := by positivity
        have h2 : 0 < (b - u) ^ 2 + v ^ 2 := by positivity
        linarith [mul_pos h1 h2]
    · have hq_nu : ¬ IsUnit q := fun hu => by
        have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
      rw [irreducible_iff] at hq_irr; push Not at hq_irr
      obtain ⟨g1, g2, hq_eq, hg1_nu, hg2_nu⟩ := hq_irr hq_nu
      have hg1_ne : g1 ≠ 0 := by rintro rfl; simp at hq_eq; exact hq_mon.ne_zero hq_eq
      have hg2_ne : g2 ≠ 0 := by rintro rfl; simp at hq_eq; exact hq_mon.ne_zero hq_eq
      have hg1_pos : 0 < g1.natDegree := by
        by_contra h0
        exact hg1_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr
          ((Polynomial.degree_eq_natDegree hg1_ne).trans (by exact_mod_cast (by omega : g1.natDegree = 0))))
      have hg2_pos : 0 < g2.natDegree := by
        by_contra h0
        exact hg2_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr
          ((Polynomial.degree_eq_natDegree hg2_ne).trans (by exact_mod_cast (by omega : g2.natDegree = 0))))
      have hdeg_sum : q.natDegree = g1.natDegree + g2.natDegree := by
        rw [hq_eq, Polynomial.natDegree_mul hg1_ne hg2_ne]
      rw [hq_eq] at hq_prod; simp only [Polynomial.eval_mul] at hq_prod
      have hprod_rearr : (g1.eval a * g1.eval b) * (g2.eval a * g2.eval b) < 0 := by linarith
      rcases mul_neg_iff.mp hprod_rearr with ⟨_, h2neg⟩ | ⟨h1neg, _⟩
      · obtain ⟨c, hc1, hc2, hce⟩ := ih g2.natDegree (by omega) g2 le_rfl a b hab h2neg
        exact ⟨c, hc1, hc2, hroot_of_q c (by rw [hq_eq, Polynomial.eval_mul, hce, mul_zero])⟩
      · obtain ⟨c, hc1, hc2, hce⟩ := ih g1.natDegree (by omega) g1 le_rfl a b hab h1neg
        exact ⟨c, hc1, hc2, hroot_of_q c (by rw [hq_eq, Polynomial.eval_mul, hce, zero_mul])⟩

/-- Ordered subfield of `AlgebraicClosure K` extending `K`. -/
structure OrderedExt (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  carrier : Subfield (AlgebraicClosure K)
  pos : Set (AlgebraicClosure K)
  pos_sub : pos ⊆ (carrier : Set (AlgebraicClosure K))
  add_mem : ∀ {a b}, a ∈ pos → b ∈ pos → a + b ∈ pos
  mul_mem : ∀ {a b}, a ∈ pos → b ∈ pos → a * b ∈ pos
  total : ∀ a ∈ carrier, a ∈ pos ∨ -a ∈ pos
  neg_one_notMem : (-1 : AlgebraicClosure K) ∉ pos
  base_sub : ∀ a : K, algebraMap K (AlgebraicClosure K) a ∈ carrier
  base_pos : ∀ a : K, 0 ≤ a → algebraMap K (AlgebraicClosure K) a ∈ pos

instance {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    PartialOrder (OrderedExt K) where
  le E1 E2 := E1.carrier ≤ E2.carrier ∧ E1.pos ⊆ E2.pos
  le_refl _ := ⟨le_rfl, Set.Subset.rfl⟩
  le_trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  le_antisymm E1 E2 h1 h2 := by
    cases E1; cases E2; congr
    · exact le_antisymm h1.1 h2.1
    · exact Set.Subset.antisymm h1.2 h2.2

lemma exists_maximal_orderedExt (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ∃ M : OrderedExt K, IsMax M := by
  let Kbar := AlgebraicClosure K
  let base : OrderedExt K :=
    { carrier := (algebraMap K Kbar).fieldRange
      pos := algebraMap K Kbar '' {a : K | 0 ≤ a}
      pos_sub := by rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩
      add_mem := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, add_nonneg ha hb, map_add _ a b⟩
      mul_mem := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a * b, mul_nonneg ha hb, map_mul _ a b⟩
      total := by
        rintro _ ⟨a, rfl⟩
        rcases le_total 0 a with h | h
        · exact Or.inl ⟨a, h, rfl⟩
        · exact Or.inr ⟨-a, neg_nonneg.mpr h, map_neg _ a⟩
      neg_one_notMem := by
        rintro ⟨a, ha, heq⟩
        have ha0 : 0 ≤ a := ha
        have ha1 : a = -1 := (algebraMap K Kbar).injective (by simpa using heq)
        linarith
      base_sub := fun a => ⟨a, rfl⟩
      base_pos := fun a ha => ⟨a, ha, rfl⟩ }
  have : Nonempty (OrderedExt K) := ⟨base⟩
  apply zorn_le_nonempty
  intro c hchain hne
  obtain ⟨E0, hE0⟩ := hne
  let carrier_sup : Subfield Kbar :=
    { carrier := ⋃ E ∈ c, (E.carrier : Set Kbar)
      zero_mem' := Set.mem_biUnion hE0 E0.carrier.zero_mem
      one_mem' := Set.mem_biUnion hE0 E0.carrier.one_mem
      add_mem' := by
        rintro a b ha hb
        rw [Set.mem_iUnion₂] at ha hb ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; obtain ⟨Eb, hEb, hb'⟩ := hb
        rcases hchain.total hEa hEb with hle | hle
        · exact ⟨Eb, hEb, Eb.carrier.add_mem (hle.1 ha') hb'⟩
        · exact ⟨Ea, hEa, Ea.carrier.add_mem ha' (hle.1 hb')⟩
      neg_mem' := by
        rintro a ha; rw [Set.mem_iUnion₂] at ha ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; exact ⟨Ea, hEa, Ea.carrier.neg_mem ha'⟩
      mul_mem' := by
        rintro a b ha hb
        rw [Set.mem_iUnion₂] at ha hb ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; obtain ⟨Eb, hEb, hb'⟩ := hb
        rcases hchain.total hEa hEb with hle | hle
        · exact ⟨Eb, hEb, Eb.carrier.mul_mem (hle.1 ha') hb'⟩
        · exact ⟨Ea, hEa, Ea.carrier.mul_mem ha' (hle.1 hb')⟩
      inv_mem' := by
        rintro a ha; rw [Set.mem_iUnion₂] at ha ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; exact ⟨Ea, hEa, Ea.carrier.inv_mem ha'⟩ }
  let Msup : OrderedExt K :=
    { carrier := carrier_sup
      pos := ⋃ E ∈ c, E.pos
      pos_sub := by
        rintro x hx; rw [Set.mem_iUnion₂] at hx
        obtain ⟨E, hE, hx'⟩ := hx; exact Set.mem_biUnion hE (E.pos_sub hx')
      add_mem := by
        rintro a b ha hb; rw [Set.mem_iUnion₂] at ha hb ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; obtain ⟨Eb, hEb, hb'⟩ := hb
        rcases hchain.total hEa hEb with hle | hle
        · exact ⟨Eb, hEb, Eb.add_mem (hle.2 ha') hb'⟩
        · exact ⟨Ea, hEa, Ea.add_mem ha' (hle.2 hb')⟩
      mul_mem := by
        rintro a b ha hb; rw [Set.mem_iUnion₂] at ha hb ⊢
        obtain ⟨Ea, hEa, ha'⟩ := ha; obtain ⟨Eb, hEb, hb'⟩ := hb
        rcases hchain.total hEa hEb with hle | hle
        · exact ⟨Eb, hEb, Eb.mul_mem (hle.2 ha') hb'⟩
        · exact ⟨Ea, hEa, Ea.mul_mem ha' (hle.2 hb')⟩
      total := by
        rintro a ha
        change a ∈ ⋃ E ∈ c, (E.carrier : Set Kbar) at ha
        rw [Set.mem_iUnion₂] at ha
        obtain ⟨E, hE, ha'⟩ := ha
        rcases E.total a ha' with h | h
        · exact Or.inl (Set.mem_biUnion hE h)
        · exact Or.inr (Set.mem_biUnion hE h)
      neg_one_notMem := by
        intro h; rw [Set.mem_iUnion₂] at h
        obtain ⟨E, _, hE⟩ := h; exact E.neg_one_notMem hE
      base_sub := fun a => Set.mem_biUnion hE0 (E0.base_sub a)
      base_pos := fun a ha => Set.mem_biUnion hE0 (E0.base_pos a ha) }
  exact ⟨Msup, fun E hE => ⟨fun _ hx => Set.mem_biUnion hE hx, fun _ hx => Set.mem_biUnion hE hx⟩⟩

lemma orderedExt_pos_zero {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : OrderedExt K) {a : M.carrier}
    (ha : (a : AlgebraicClosure K) ∈ M.pos) (hna : ((-a : M.carrier) : AlgebraicClosure K) ∈ M.pos) :
    a = 0 := by
  by_contra ha0
  have ha1_ne : (a : AlgebraicClosure K) ≠ 0 := fun h => ha0 (Subtype.ext h)
  rcases M.total (a : AlgebraicClosure K)⁻¹ (M.carrier.inv_mem a.2) with hinv | hninv
  · exact M.neg_one_notMem (by
      have := M.mul_mem hna hinv; simpa [neg_mul, mul_inv_cancel₀ ha1_ne] using this)
  · exact M.neg_one_notMem (by
      have := M.mul_mem ha hninv; simpa [mul_neg, mul_inv_cancel₀ ha1_ne] using this)

lemma maximal_orderedExt_no_ext {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : OrderedExt K) (hMmax : IsMax M)
    (E' : Subfield (AlgebraicClosure K)) (hle : M.carrier ≤ E')
    (hnot : (-1 : E') ∉ {z : E' | ∃ (l : List (M.carrier × E')),
      (∀ p ∈ l, (p.1 : AlgebraicClosure K) ∈ M.pos) ∧
      z = (l.map fun p => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum}) :
    E' = M.carrier := by
  let Kbar := AlgebraicClosure K
  let T : Set E' := {z : E' | ∃ (l : List (M.carrier × E')),
    (∀ p ∈ l, (p.1 : Kbar) ∈ M.pos) ∧
    z = (l.map fun p => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum}
  have h1pos : (1 : Kbar) ∈ M.pos := by
    rcases M.total 1 M.carrier.one_mem with h | h
    · exact h
    · simpa using M.mul_mem h h
  have hT_add : ∀ {a b : E'}, a ∈ T → b ∈ T → a + b ∈ T := by
    rintro _ _ ⟨l1, h1, rfl⟩ ⟨l2, h2, rfl⟩
    refine ⟨l1 ++ l2, fun p hp => (List.mem_append.mp hp).elim (h1 p) (h2 p), ?_⟩
    simp [List.map_append, List.sum_append]
  have hT_mul : ∀ {a b : E'}, a ∈ T → b ∈ T → a * b ∈ T := by
    rintro _ _ ⟨l1, h1, rfl⟩ ⟨l2, h2, rfl⟩
    refine ⟨l1.flatMap (fun p => l2.map (fun q => (p.1 * q.1, p.2 * q.2))), ?_, ?_⟩
    · intro r hr
      rw [List.mem_flatMap] at hr; obtain ⟨p, hp, hr⟩ := hr
      rw [List.mem_map] at hr; obtain ⟨q, hq, rfl⟩ := hr
      exact M.mul_mem (h1 p hp) (h2 q hq)
    · have hdist : ∀ (p : M.carrier × E') (ls : List (M.carrier × E')),
          (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2 *
            (ls.map fun q => (⟨q.1.1, hle q.1.2⟩ : E') * q.2 ^ 2).sum =
          ((ls.map fun q => (p.1 * q.1, p.2 * q.2)).map
            fun q => (⟨q.1.1, hle q.1.2⟩ : E') * q.2 ^ 2).sum := by
        intro p ls
        induction ls with
        | nil => simp
        | cons q ls ih2 =>
          simp only [List.map_cons, List.sum_cons, mul_add]
          rw [ih2]; congr 1; ext; push_cast; ring
      clear h1 h2
      induction l1 with
      | nil => simp
      | cons p l1 ih =>
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
          List.sum_append, add_mul]
        rw [ih, hdist]
  have hT_sq : ∀ a : E', a ^ 2 ∈ T := fun a => ⟨[(1, a)], by simp [h1pos], by ext; simp⟩
  obtain ⟨P', hTP', hP'_add, hP'_mul, hP'_tot, hP'_neg1⟩ :=
    exists_total_ordering_of_preordering T hT_add hT_mul hT_sq hnot
  let M' : OrderedExt K :=
    { carrier := E'
      pos := Subtype.val '' P'
      pos_sub := by rintro _ ⟨x, _, rfl⟩; exact x.2
      add_mem := by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, hP'_add hx hy, rfl⟩
      mul_mem := by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x * y, hP'_mul hx hy, rfl⟩
      total := fun a ha => by
        rcases hP'_tot ⟨a, ha⟩ with h | h
        · exact Or.inl ⟨⟨a, ha⟩, h, rfl⟩
        · exact Or.inr ⟨-⟨a, ha⟩, h, rfl⟩
      neg_one_notMem := by
        rintro ⟨x, hx, heq⟩; exact hP'_neg1 ((Subtype.ext heq : x = -1) ▸ hx)
      base_sub := fun a => hle (M.base_sub a)
      base_pos := fun a ha => ⟨⟨algebraMap K Kbar a, hle (M.base_sub a)⟩,
        hTP' ⟨[(⟨algebraMap K Kbar a, M.base_sub a⟩, 1)], by simp; exact M.base_pos a ha, by ext; simp⟩, rfl⟩ }
  have hMM' : M ≤ M' := ⟨hle, fun x hx => ⟨⟨x, hle (M.pos_sub hx)⟩,
    hTP' ⟨[(⟨x, M.pos_sub hx⟩, 1)], by simp [hx], by ext; simp⟩, rfl⟩⟩
  exact le_antisymm (hMmax hMM').1 hle

lemma maximal_orderedExt_sq {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : OrderedExt K) (hMmax : IsMax M) :
    letI : LinearOrder M.carrier :=
      linearOrderOfPosCone {x : M.carrier | (x : AlgebraicClosure K) ∈ M.pos}
        (fun ha hb => M.add_mem ha hb) (fun a => M.total a.1 a.2)
        (fun ha hna => orderedExt_pos_zero M ha hna)
    ∀ a : M.carrier, 0 ≤ a → ∃ r : M.carrier, r ^ 2 = a := by
  let Kbar := AlgebraicClosure K
  let R := M.carrier
  let PR : Set R := {x : R | (x : Kbar) ∈ M.pos}
  let : LinearOrder R :=
    linearOrderOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun a => M.total a.1 a.2)
      (fun ha hna => orderedExt_pos_zero M ha hna)
  have : IsStrictOrderedRing R :=
    isStrictOrderedRingOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun ha hb => M.mul_mem ha hb)
      (fun a => M.total a.1 a.2) (fun ha hna => orderedExt_pos_zero M ha hna)
  have hnonneg_iff : ∀ a : R, 0 ≤ a ↔ (a : Kbar) ∈ M.pos := fun a => by
    change a - 0 ∈ PR ↔ (a : Kbar) ∈ M.pos; simp [PR]
  intro a ha
  by_contra hnosq; push Not at hnosq
  have hpoly : (Polynomial.X ^ 2 - Polynomial.C (a : Kbar)).degree ≠ 0 := by
    have hd : (Polynomial.X ^ 2 - Polynomial.C (a : Kbar)).natDegree = 2 := by compute_degree!
    rw [Polynomial.degree_eq_natDegree (by intro h0; rw [h0] at hd; simp at hd), hd]; norm_num
  obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 - Polynomial.C (a : Kbar)) hpoly
  have hα_sq : α ^ 2 = (a : Kbar) := by
    have : α ^ 2 - (a : Kbar) = 0 := by simpa [Polynomial.IsRoot] using hα_root
    linear_combination this
  have hα_notMem : α ∉ M.carrier := fun hmem => hnosq ⟨α, hmem⟩ (Subtype.ext hα_sq)
  let E' : Subfield Kbar :=
    { carrier := {z | ∃ u v : R, z = (u : Kbar) + (v : Kbar) * α}
      zero_mem' := ⟨0, 0, by simp⟩
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by rintro _ _ ⟨u1, v1, rfl⟩ ⟨u2, v2, rfl⟩; exact ⟨u1 + u2, v1 + v2, by push_cast; ring⟩
      neg_mem' := by rintro _ ⟨u, v, rfl⟩; exact ⟨-u, -v, by push_cast; ring⟩
      mul_mem' := by
        rintro _ _ ⟨u1, v1, rfl⟩ ⟨u2, v2, rfl⟩
        refine ⟨u1 * u2 + a * v1 * v2, u1 * v2 + v1 * u2, ?_⟩
        push_cast; linear_combination ((v1 : Kbar) * (v2 : Kbar)) * hα_sq
      inv_mem' := by
        rintro _ ⟨u, v, rfl⟩
        by_cases h0 : u = 0 ∧ v = 0
        · rcases h0 with ⟨rfl, rfl⟩; exact ⟨0, 0, by simp⟩
        · have hd : u ^ 2 - a * v ^ 2 ≠ 0 := by
            intro hdiff
            by_cases hv : v = 0
            · subst hv; exact h0 ⟨sq_eq_zero_iff.mp (by simpa using hdiff), rfl⟩
            · exact hnosq (u / v) (by field_simp [hv]; linear_combination hdiff)
          refine ⟨u / (u ^ 2 - a * v ^ 2), -v / (u ^ 2 - a * v ^ 2), ?_⟩
          have hdK : ((u ^ 2 - a * v ^ 2 : R) : Kbar) ≠ 0 :=
            fun h => hd (Subtype.ext (by simpa using h))
          have hmul1 : ((u : Kbar) + (v : Kbar) * α) *
              (((u / (u ^ 2 - a * v ^ 2) : R) : Kbar) +
                ((-v / (u ^ 2 - a * v ^ 2) : R) : Kbar) * α) = 1 := by
            have hnum : ((u : Kbar) + (v : Kbar) * α) * ((u : Kbar) + -(v : Kbar) * α) =
                ((u ^ 2 - a * v ^ 2 : R) : Kbar) := by
              push_cast; linear_combination -(v : Kbar) ^ 2 * hα_sq
            push_cast
            calc ((u : Kbar) + (v : Kbar) * α) *
                  ((u : Kbar) / ((u : Kbar) ^ 2 - (a : Kbar) * (v : Kbar) ^ 2) +
                    -(v : Kbar) / ((u : Kbar) ^ 2 - (a : Kbar) * (v : Kbar) ^ 2) * α)
                = (((u : Kbar) + (v : Kbar) * α) * ((u : Kbar) + -(v : Kbar) * α)) /
                    ((u : Kbar) ^ 2 - (a : Kbar) * (v : Kbar) ^ 2) := by ring
              _ = ((u ^ 2 - a * v ^ 2 : R) : Kbar) / ((u ^ 2 - a * v ^ 2 : R) : Kbar) := by
                  rw [hnum]; push_cast; rfl
              _ = 1 := div_self hdK
          exact inv_eq_of_mul_eq_one_right hmul1 }
  have hle : M.carrier ≤ E' := fun x hx => ⟨⟨x, hx⟩, 0, by simp⟩
  have hlin_ind : ∀ u v : R, (u : Kbar) + (v : Kbar) * α = 0 → u = 0 ∧ v = 0 := by
    intro u v heq
    by_cases hv : v = 0
    · subst hv; exact ⟨Subtype.ext (by simpa using heq), rfl⟩
    · exfalso
      have hvK : (v : Kbar) ≠ 0 := fun h => hv (Subtype.ext h)
      have hαeq : α = ((-u / v : R) : Kbar) := by
        push_cast; exact eq_div_of_mul_eq hvK (by linear_combination heq)
      exact hα_notMem (hαeq ▸ (-u / v).2)
  have hnot : (-1 : E') ∉ {z : E' | ∃ (l : List (R × E')),
      (∀ p ∈ l, (p.1 : Kbar) ∈ M.pos) ∧
      z = (l.map fun p => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum} := by
    rintro ⟨l, hl_nn, heq⟩
    have hdecomp : ∀ (l' : List (R × E')), (∀ p ∈ l', (p.1 : Kbar) ∈ M.pos) →
        ∃ s t : R, 0 ≤ s ∧
          ((l'.map fun (p : R × E') => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum).val =
            (s : Kbar) + (t : Kbar) * α := by
      intro l'
      induction l' with
      | nil => intro _; exact ⟨0, 0, le_rfl, by simp⟩
      | cons p l' ih =>
        intro hnn
        obtain ⟨s, t, hs, hst⟩ := ih (fun q hq => hnn q (List.mem_cons_of_mem _ hq))
        obtain ⟨u, v, huv⟩ := p.2.2
        have hp0 : 0 ≤ p.1 := (hnonneg_iff p.1).mpr (hnn p (List.mem_cons_self ..))
        refine ⟨p.1 * (u ^ 2 + a * v ^ 2) + s, 2 * p.1 * u * v + t, ?_, ?_⟩
        · have : 0 ≤ u ^ 2 + a * v ^ 2 := by positivity
          exact add_nonneg (mul_nonneg hp0 this) hs
        · have hcons :
              (((p :: l').map fun (x : R × E') => (⟨x.1.1, hle x.1.2⟩ : E') * x.2 ^ 2).sum).val =
              (p.1 : Kbar) * (p.2 : Kbar) ^ 2 +
                ((l'.map fun (x : R × E') => (⟨x.1.1, hle x.1.2⟩ : E') * x.2 ^ 2).sum).val := by
            simp only [List.map_cons, List.sum_cons]; rfl
          rw [hcons, hst, huv]; push_cast
          have h2 : ((2 : R) : Kbar) = 2 := map_ofNat M.carrier.subtype 2
          rw [h2]
          linear_combination (p.1 : Kbar) * (v : Kbar) ^ 2 * hα_sq
    obtain ⟨s, t, hs, hst⟩ := hdecomp l hl_nn
    have hval : (-1 : Kbar) = (s : Kbar) + (t : Kbar) * α := by
      have hsub : ((-1 : E')).val =
          ((l.map fun (p : R × E') => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum).val :=
        congr_arg Subtype.val heq
      rw [← hst]; exact hsub
    have h0 : ((s + 1 : R) : Kbar) + (t : Kbar) * α = 0 := by push_cast; linear_combination -hval
    have hs1 : s + 1 = 0 := (hlin_ind (s + 1) t h0).1
    linarith
  have hE'eq : E' = M.carrier := maximal_orderedExt_no_ext M hMmax E' hle hnot
  exact hα_notMem (hE'eq ▸ ⟨0, 1, by simp⟩)

lemma poly_list_sum_deg_even {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l : List (R × Polynomial R)) (hne : l ≠ [])
    (hl : ∀ p ∈ l, 0 < p.1 ∧ p.2 ≠ 0) :
    ∃ k : ℕ, (∀ p ∈ l, p.2.natDegree ≤ k) ∧ (∃ p ∈ l, p.2.natDegree = k) ∧
      ((1 : Polynomial R) + (l.map fun (p : R × Polynomial R) => Polynomial.C p.1 * p.2 ^ 2).sum).natDegree = 2 * k := by
  let k : ℕ := (l.map fun p => p.2.natDegree).foldr max 0
  have hk_le : ∀ p ∈ l, p.2.natDegree ≤ k := by
    intro p hp
    dsimp [k]
    have hmem : p.2.natDegree ∈ l.map (fun p => p.2.natDegree) := List.mem_map.mpr ⟨p, hp, rfl⟩
    generalize l.map (fun p => p.2.natDegree) = ns at hmem ⊢
    induction ns with
    | nil => cases hmem
    | cons a ns ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact le_max_left _ _
      · exact le_trans (ih hmem') (le_max_right _ _)
  have hk_exists : ∃ p ∈ l, p.2.natDegree = k := by
    suffices ∀ (ns : List ℕ), ns ≠ [] → ns.foldr max 0 ∈ ns by
      obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp (this _ (by simpa using hne))
      exact ⟨p, hp, hpeq⟩
    intro ns hns
    induction ns with
    | nil => exact absurd rfl hns
    | cons a ns ih =>
      cases ns with
      | nil => simp
      | cons b ns' =>
        change max a (List.foldr max 0 (b :: ns')) ∈ a :: b :: ns'
        rcases max_choice a (List.foldr max 0 (b :: ns')) with h | h <;> rw [h]
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih (List.cons_ne_nil b ns'))
  have hlist_coeff : ∀ (ls : List (Polynomial R)) (m : ℕ),
      ls.sum.coeff m = (ls.map fun P => P.coeff m).sum := by
    intro ls m; induction ls with
    | nil => simp
    | cons P ls ih => simp [ih]
  let H : Polynomial R := 1 + (l.map fun p => Polynomial.C p.1 * p.2 ^ 2).sum
  have hcoeff_gt : ∀ m, 2 * k < m → H.coeff m = 0 := by
    intro m hm
    dsimp [H]
    rw [Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), zero_add, hlist_coeff]
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx; obtain ⟨_, hP, rfl⟩ := hx
    rw [List.mem_map] at hP; obtain ⟨p, hp, rfl⟩ := hP
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (Polynomial.C p.1 * p.2 ^ 2).natDegree
        ≤ (Polynomial.C p.1).natDegree + (p.2 ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + 2 * p.2.natDegree := by
          rw [Polynomial.natDegree_C]; exact Nat.add_le_add_left Polynomial.natDegree_pow_le 0
      _ ≤ 2 * k := by have := hk_le p hp; omega
      _ < m := hm
  have hcoeff_pos : 0 < H.coeff (2 * k) := by
    have hterm_nn : ∀ p ∈ l, 0 ≤ (Polynomial.C p.1 * p.2 ^ 2).coeff (2 * k) := by
      intro p hp
      by_cases hpeq : p.2.natDegree = k
      · have hdeg2 : (p.2 ^ 2).natDegree = 2 * k := by rw [Polynomial.natDegree_pow, hpeq]
        rw [Polynomial.coeff_C_mul, ← hdeg2, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow]
        exact mul_nonneg (le_of_lt (hl p hp).1) (sq_nonneg _)
      · have hlt : p.2.natDegree < k := lt_of_le_of_ne (hk_le p hp) hpeq
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
          calc (Polynomial.C p.1 * p.2 ^ 2).natDegree
              ≤ (Polynomial.C p.1).natDegree + (p.2 ^ 2).natDegree := Polynomial.natDegree_mul_le
            _ ≤ 0 + 2 * p.2.natDegree := by
                rw [Polynomial.natDegree_C]; exact Nat.add_le_add_left Polynomial.natDegree_pow_le 0
            _ < 2 * k := by omega)]
    obtain ⟨p0, hp0, hp0k⟩ := hk_exists
    have hp0_pos : 0 < (Polynomial.C p0.1 * p0.2 ^ 2).coeff (2 * k) := by
      have hdeg2 : (p0.2 ^ 2).natDegree = 2 * k := by rw [Polynomial.natDegree_pow, hp0k]
      rw [Polynomial.coeff_C_mul, ← hdeg2, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow]
      exact mul_pos (hl p0 hp0).1
        (sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (hl p0 hp0).2))
    have hsum_pos : 0 < ((l.map fun (p : R × Polynomial R) => Polynomial.C p.1 * p.2 ^ 2).sum).coeff (2 * k) := by
      rw [hlist_coeff]
      suffices ∀ (ls : List (R × Polynomial R)),
          (∀ p ∈ ls, 0 ≤ (Polynomial.C p.1 * p.2 ^ 2).coeff (2 * k)) →
          (∃ p ∈ ls, 0 < (Polynomial.C p.1 * p.2 ^ 2).coeff (2 * k)) →
          0 < ((ls.map fun p => Polynomial.C p.1 * p.2 ^ 2).map fun P => P.coeff (2 * k)).sum from
        this l hterm_nn ⟨p0, hp0, hp0_pos⟩
      intro ls
      induction ls with
      | nil => rintro _ ⟨_, h, _⟩; simp at h
      | cons p ls ih =>
        intro hnn ⟨x, hx, hxpos⟩
        simp only [List.map_cons, List.sum_cons]
        have hp_nn := hnn p (List.mem_cons_self ..)
        have hls_nn : 0 ≤ ((ls.map fun p => Polynomial.C p.1 * p.2 ^ 2).map
            fun P => P.coeff (2 * k)).sum := by
          apply List.sum_nonneg; intro y hy
          rw [List.mem_map] at hy; obtain ⟨_, hP, rfl⟩ := hy
          rw [List.mem_map] at hP; obtain ⟨q, hq, rfl⟩ := hP
          exact hnn q (List.mem_cons_of_mem _ hq)
        rcases List.mem_cons.mp hx with rfl | hx'
        · linarith
        · have := ih (fun y hy => hnn y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hxpos⟩; linarith
    dsimp [H]; rw [Polynomial.coeff_add, Polynomial.coeff_one]; split_ifs <;> linarith
  refine ⟨k, hk_le, hk_exists, le_antisymm ?_ ?_⟩
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; exact hcoeff_gt
  · exact Polynomial.le_natDegree_of_ne_zero (ne_of_gt hcoeff_pos)

lemma maximal_orderedExt_odd_root {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : OrderedExt K) (hMmax : IsMax M) :
    letI : LinearOrder M.carrier :=
      linearOrderOfPosCone {x : M.carrier | (x : AlgebraicClosure K) ∈ M.pos}
        (fun ha hb => M.add_mem ha hb) (fun a => M.total a.1 a.2)
        (fun ha hna => orderedExt_pos_zero M ha hna)
    ∀ f : Polynomial M.carrier, Odd f.natDegree → ∃ r : M.carrier, f.eval r = 0 := by
  let Kbar := AlgebraicClosure K
  let R := M.carrier
  let PR : Set R := {x : R | (x : Kbar) ∈ M.pos}
  let : LinearOrder R :=
    linearOrderOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun a => M.total a.1 a.2)
      (fun ha hna => orderedExt_pos_zero M ha hna)
  have : IsStrictOrderedRing R :=
    isStrictOrderedRingOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun ha hb => M.mul_mem ha hb)
      (fun a => M.total a.1 a.2) (fun ha hna => orderedExt_pos_zero M ha hna)
  have hnonneg_iff : ∀ a : R, 0 ≤ a ↔ (a : Kbar) ∈ M.pos := fun a => by
    change a - 0 ∈ PR ↔ (a : Kbar) ∈ M.pos; simp [PR]
  suffices ∀ d : ℕ, ∀ f : Polynomial R, f.natDegree ≤ d → Odd f.natDegree →
      ∃ r : R, f.eval r = 0 by
    intro f hf; exact this f.natDegree f le_rfl hf
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hdeg hf_odd
    have hf_ne : f ≠ 0 := by rintro rfl; simp at hf_odd
    let c := f.leadingCoeff
    have hc_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
    let q := Polynomial.C c⁻¹ * f
    have hq_mon : q.Monic := by
      dsimp [q]; rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hc_ne
    have hq_deg : q.natDegree = f.natDegree := by
      dsimp [q]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hc_ne)]
    have hq_odd : Odd q.natDegree := hq_deg ▸ hf_odd
    have hroot_of_q : ∀ x, q.eval x = 0 → f.eval x = 0 := by
      intro x hx; dsimp [q] at hx; simp only [Polynomial.eval_mul, Polynomial.eval_C] at hx
      exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero hc_ne)
    by_cases hq_deg1 : q.natDegree = 1
    · refine ⟨-q.coeff 0, hroot_of_q _ ?_⟩
      have hq_lin : q = Polynomial.X + Polynomial.C (q.coeff 0) := by
        ext k
        by_cases hk0 : k = 0
        · subst hk0; simp
        by_cases hk1 : k = 1
        · subst hk1
          have hlead : q.coeff 1 = 1 := hq_deg1 ▸ hq_mon.leadingCoeff
          rw [hlead]; simp
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X, Polynomial.coeff_C, hk0, Ne.symm hk1]
      rw [hq_lin]; simp
    · have hq_ge3 : 3 ≤ q.natDegree := by obtain ⟨m, hm⟩ := hq_odd; omega
      by_cases hq_irr : Irreducible q
      · let qK : Polynomial Kbar := q.map (algebraMap R Kbar)
        have hqK_deg : qK.natDegree = q.natDegree :=
          Polynomial.natDegree_map_eq_of_injective (algebraMap R Kbar).injective q
        have hqK_ne : qK ≠ 0 := by intro h0; rw [h0] at hqK_deg; simp at hqK_deg; omega
        obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root qK (by
          rw [Polynomial.degree_eq_natDegree hqK_ne, hqK_deg]
          exact_mod_cast (by omega : q.natDegree ≠ 0))
        have hq_aeval : Polynomial.aeval α q = 0 := by
          simpa [qK, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hα_root
        have hα_notMem : α ∉ M.carrier := by
          intro hmem
          let αR : R := ⟨α, hmem⟩
          have hr : q.eval αR = 0 := by
            have h1 : algebraMap R Kbar (q.eval αR) = 0 := by
              have h2 : (q.map (algebraMap R Kbar)).eval (algebraMap R Kbar αR) =
                  algebraMap R Kbar (q.eval αR) := by
                rw [Polynomial.eval_map]
                exact (Polynomial.hom_eval₂ q (RingHom.id R) (algebraMap R Kbar) αR).symm
              rw [← h2]; exact hα_root
            exact (algebraMap R Kbar).injective (by simpa using h1)
          have hdvd : Polynomial.X - Polynomial.C αR ∣ q := Polynomial.dvd_iff_isRoot.mpr hr
          have hnu : ¬ IsUnit (Polynomial.X - Polynomial.C αR) := by
            intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
            rw [Polynomial.natDegree_X_sub_C] at this; omega
          rcases hq_irr.dvd_iff.mp hdvd with h1 | h2
          · exact hnu h1
          · have := Polynomial.natDegree_le_of_dvd h2.dvd (Polynomial.X_sub_C_ne_zero _)
            rw [Polynomial.natDegree_X_sub_C] at this; omega
        have hker_dvd : ∀ p : Polynomial R, Polynomial.aeval α p = 0 → q ∣ p := by
          intro p hp
          by_contra hndvd
          obtain ⟨a, b, hab⟩ := hq_irr.coprime_iff_not_dvd.mpr hndvd
          have h1 := congr_arg (Polynomial.aeval α) hab
          simp only [map_add, map_mul, map_one, hq_aeval, hp, mul_zero, add_zero] at h1
          exact zero_ne_one h1
        let evα : Polynomial R →+* Kbar := (Polynomial.aeval (R := R) α).toRingHom
        let E' : Subfield Kbar :=
          { carrier := Set.range evα
            zero_mem' := ⟨0, map_zero _⟩
            one_mem' := ⟨1, map_one _⟩
            add_mem' := by rintro _ _ ⟨p1, rfl⟩ ⟨p2, rfl⟩; exact ⟨p1 + p2, map_add _ _ _⟩
            neg_mem' := by rintro _ ⟨p1, rfl⟩; exact ⟨-p1, map_neg _ _⟩
            mul_mem' := by rintro _ _ ⟨p1, rfl⟩ ⟨p2, rfl⟩; exact ⟨p1 * p2, map_mul _ _ _⟩
            inv_mem' := by
              rintro _ ⟨p1, rfl⟩
              by_cases h0 : evα p1 = 0
              · rw [h0, inv_zero]; exact ⟨0, map_zero _⟩
              · have hndvd : ¬ q ∣ p1 := fun ⟨w, hw⟩ =>
                  h0 (by rw [hw]; change Polynomial.aeval α (q * w) = 0; simp [hq_aeval])
                obtain ⟨a, b, hab⟩ := hq_irr.coprime_iff_not_dvd.mpr hndvd
                refine ⟨b, ?_⟩
                have h1 : evα a * evα q + evα b * evα p1 = 1 := by
                  have := congr_arg evα hab
                  simpa only [map_add, map_mul, map_one] using this
                have hq0 : evα q = 0 := hq_aeval
                rw [hq0, mul_zero, zero_add] at h1
                exact (inv_eq_of_mul_eq_one_left h1).symm }
        have hle : M.carrier ≤ E' := fun x hx =>
          ⟨Polynomial.C (⟨x, hx⟩ : R), by
            change Polynomial.aeval α (Polynomial.C (⟨x, hx⟩ : R)) = x
            rw [Polynomial.aeval_C]; rfl⟩
        have hnot : (-1 : E') ∉ {z : E' | ∃ (l : List (R × E')),
            (∀ p ∈ l, (p.1 : Kbar) ∈ M.pos) ∧
            z = (l.map fun p => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum} := by
          rintro ⟨l, hl_nn, heq⟩
          have hlift : ∀ (l0 : List (R × E')), (∀ p ∈ l0, (p.1 : Kbar) ∈ M.pos) →
              ∃ (l' : List (R × Polynomial R)),
                (∀ p ∈ l', 0 < p.1 ∧ p.2 ≠ 0 ∧ p.2.natDegree < q.natDegree) ∧
                ((l0.map fun (p : R × E') => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum).val =
                  Polynomial.aeval α (l'.map fun p => Polynomial.C p.1 * p.2 ^ 2).sum := by
            intro l0
            induction l0 with
            | nil => intro _; exact ⟨[], by simp, by simp⟩
            | cons p l0 ih' =>
              intro hnn
              obtain ⟨l', hl', hl'eq⟩ := ih' (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
              obtain ⟨u, hu⟩ := p.2.2
              let r := u %ₘ q
              have hr_aeval : Polynomial.aeval α r = p.2.1 := by
                have h1 := congr_arg (Polynomial.aeval α) (Polynomial.modByMonic_add_div u q)
                rw [map_add, map_mul, hq_aeval, zero_mul, add_zero] at h1
                exact h1.trans hu
              have hp0 : 0 ≤ p.1 := (hnonneg_iff p.1).mpr (hnn p (List.mem_cons_self ..))
              have hcons_val :
                  (((p :: l0).map fun (x : R × E') => (⟨x.1.1, hle x.1.2⟩ : E') * x.2 ^ 2).sum).val =
                  (p.1 : Kbar) * (p.2 : Kbar) ^ 2 +
                    ((l0.map fun (x : R × E') => (⟨x.1.1, hle x.1.2⟩ : E') * x.2 ^ 2).sum).val := by
                simp only [List.map_cons, List.sum_cons]
                rfl
              by_cases hskip : p.1 = 0 ∨ r = 0
              · refine ⟨l', hl', ?_⟩
                rw [hcons_val, hl'eq]
                rcases hskip with h1 | h2
                · have : (p.1 : Kbar) = 0 := by simp [h1]
                  simp [this]
                · have : (p.2 : Kbar) = 0 := by rw [← hr_aeval, h2, map_zero]
                  simp [this]
              · push Not at hskip
                refine ⟨(p.1, r) :: l', ?_, ?_⟩
                · intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · exact ⟨lt_of_le_of_ne hp0 (Ne.symm hskip.1), hskip.2,
                      Polynomial.natDegree_modByMonic_lt u hq_mon
                        (fun h1 => by rw [h1] at hq_ge3; simp at hq_ge3)⟩
                  · exact hl' x hx'
                · rw [hcons_val, hl'eq]
                  simp only [List.map_cons, List.sum_cons, map_add, map_mul, map_pow,
                    Polynomial.aeval_C, hr_aeval]
                  rfl
          obtain ⟨l', hl', hl'eq⟩ := hlift l hl_nn
          let H : Polynomial R := 1 + (l'.map fun p => Polynomial.C p.1 * p.2 ^ 2).sum
          have hH_aeval : Polynomial.aeval α H = 0 := by
            have hval : (-1 : Kbar) =
                Polynomial.aeval α (l'.map fun p => Polynomial.C p.1 * p.2 ^ 2).sum := by
              have hsub : ((-1 : E')).val =
                  ((l.map fun (p : R × E') => (⟨p.1.1, hle p.1.2⟩ : E') * p.2 ^ 2).sum).val :=
                congr_arg Subtype.val heq
              rw [← hl'eq]; exact hsub
            dsimp [H]; rw [map_add, map_one, ← hval]; ring
          obtain ⟨g, hHg⟩ := hker_dvd H hH_aeval
          have hl'_ne : l' ≠ [] := by
            intro hnil; subst hnil
            have h1 : (1 : Polynomial R) = q * g := by simpa [H] using hHg
            exact hq_irr.not_isUnit (isUnit_iff_exists_inv.mpr ⟨g, h1.symm⟩)
          obtain ⟨k, _, ⟨p0, hp0, hp0k⟩, hH_deg⟩ :=
            poly_list_sum_deg_even l' hl'_ne (fun p hp => ⟨(hl' p hp).1, (hl' p hp).2.1⟩)
          have hk_lt : k < q.natDegree := hp0k ▸ (hl' p0 hp0).2.2
          have hH_ne : H ≠ 0 := by
            intro h0
            have hval0 : H.eval 0 = 0 := by rw [h0, Polynomial.eval_zero]
            have hpos : 0 < H.eval 0 := by
              dsimp [H]; rw [Polynomial.eval_add, Polynomial.eval_one]
              have hev : ∀ (ls : List (Polynomial R)), ls.sum.eval 0 = (ls.map fun P => P.eval 0).sum := by
                intro ls; induction ls with | nil => simp | cons P ls ih' => simp [ih']
              rw [hev]
              have hnn : 0 ≤ ((l'.map fun p => Polynomial.C p.1 * p.2 ^ 2).map fun P => P.eval 0).sum := by
                apply List.sum_nonneg; intro x hx
                rw [List.mem_map] at hx; obtain ⟨_, hP, rfl⟩ := hx
                rw [List.mem_map] at hP; obtain ⟨p, hp, rfl⟩ := hP
                simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
                exact mul_nonneg (le_of_lt (hl' p hp).1) (sq_nonneg _)
              linarith
            linarith
          have hg_ne : g ≠ 0 := by rintro rfl; simp at hHg; exact hH_ne hHg
          have hg_deg_sum : 2 * k = q.natDegree + g.natDegree := by
            have h1 : H.natDegree = q.natDegree + g.natDegree := by
              rw [hHg, Polynomial.natDegree_mul hq_mon.ne_zero hg_ne]
            rw [← h1]; exact hH_deg.symm
          have hg_odd : Odd g.natDegree := by
            obtain ⟨m, hm⟩ := hq_odd; refine ⟨k - m - 1, ?_⟩; omega
          obtain ⟨β, hβ⟩ := ih g.natDegree (by omega) g le_rfl hg_odd
          have hHβ : H.eval β = 0 := by rw [hHg, Polynomial.eval_mul, hβ, mul_zero]
          have hHβ_pos : 0 < H.eval β := by
            dsimp [H]; rw [Polynomial.eval_add, Polynomial.eval_one]
            have hev : ∀ (ls : List (Polynomial R)), ls.sum.eval β = (ls.map fun P => P.eval β).sum := by
              intro ls; induction ls with | nil => simp | cons P ls ih' => simp [ih']
            rw [hev]
            have hnn : 0 ≤ ((l'.map fun p => Polynomial.C p.1 * p.2 ^ 2).map fun P => P.eval β).sum := by
              apply List.sum_nonneg; intro x hx
              rw [List.mem_map] at hx; obtain ⟨_, hP, rfl⟩ := hx
              rw [List.mem_map] at hP; obtain ⟨p, hp, rfl⟩ := hP
              simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
              exact mul_nonneg (le_of_lt (hl' p hp).1) (sq_nonneg _)
            linarith
          linarith
        have hE'eq : E' = M.carrier := maximal_orderedExt_no_ext M hMmax E' hle hnot
        exact False.elim (hα_notMem (hE'eq ▸ ⟨Polynomial.X, by change Polynomial.aeval α Polynomial.X = α; simp⟩))
      · have hq_nu : ¬ IsUnit q := fun hu => by
          have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
        rw [irreducible_iff] at hq_irr; push Not at hq_irr
        obtain ⟨g1, g2, hq_eq, hg1_nu, hg2_nu⟩ := hq_irr hq_nu
        have hg1_ne : g1 ≠ 0 := by rintro rfl; simp at hq_eq; exact hq_mon.ne_zero hq_eq
        have hg2_ne : g2 ≠ 0 := by rintro rfl; simp at hq_eq; exact hq_mon.ne_zero hq_eq
        have hg1_pos : 0 < g1.natDegree := by
          by_contra h0
          exact hg1_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr
            ((Polynomial.degree_eq_natDegree hg1_ne).trans (by exact_mod_cast (by omega : g1.natDegree = 0))))
        have hg2_pos : 0 < g2.natDegree := by
          by_contra h0
          exact hg2_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr
            ((Polynomial.degree_eq_natDegree hg2_ne).trans (by exact_mod_cast (by omega : g2.natDegree = 0))))
        have hdeg_sum : q.natDegree = g1.natDegree + g2.natDegree := by
          rw [hq_eq, Polynomial.natDegree_mul hg1_ne hg2_ne]
        rcases Nat.even_or_odd g1.natDegree with ⟨a, ha⟩ | h1o
        · obtain ⟨b, hb⟩ := hq_odd
          obtain ⟨r, hr⟩ := ih g2.natDegree (by omega) g2 le_rfl ⟨b - a, by omega⟩
          exact ⟨r, hroot_of_q r (by rw [hq_eq, Polynomial.eval_mul, hr, mul_zero])⟩
        · obtain ⟨r, hr⟩ := ih g1.natDegree (by omega) g1 le_rfl h1o
          exact ⟨r, hroot_of_q r (by rw [hq_eq, Polynomial.eval_mul, hr, zero_mul])⟩

/-- Every linearly ordered field embeds into a real closed field satisfying `HasPolyIVT`. -/
lemma exists_real_closure (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ∃ (R : Type) (_ : Field R) (_ : LinearOrder R) (_ : IsStrictOrderedRing R)
      (_ : HasPolyIVT R) (emb : K →+* R),
      ∀ a : K, 0 ≤ a → 0 ≤ emb a := by
  obtain ⟨M, hMmax⟩ := exists_maximal_orderedExt K
  let R : Type := M.carrier
  let PR : Set R := {x : R | (x : AlgebraicClosure K) ∈ M.pos}
  let : LinearOrder R :=
    linearOrderOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun a => M.total a.1 a.2)
      (fun ha hna => orderedExt_pos_zero M ha hna)
  have : IsStrictOrderedRing R :=
    isStrictOrderedRingOfPosCone PR (fun ha hb => M.add_mem ha hb) (fun ha hb => M.mul_mem ha hb)
      (fun a => M.total a.1 a.2) (fun ha hna => orderedExt_pos_zero M ha hna)
  have : HasPolyIVT R :=
    hasPolyIVT_of_realClosed (maximal_orderedExt_sq M hMmax) (maximal_orderedExt_odd_root M hMmax)
  let emb : K →+* R := (algebraMap K (AlgebraicClosure K)).codRestrict M.carrier M.base_sub
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, emb, ?_⟩
  intro a ha
  change emb a - 0 ∈ PR
  simp only [sub_zero, PR, Set.mem_ofPred_eq]
  exact M.base_pos a ha

/-! ### Part C: Tarski–Seidenberg Transfer Principle (Cohen–Hörmander) -/

inductive RSign
  | neg | zero | pos
  deriving DecidableEq

def RSign.negate : RSign → RSign
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

noncomputable def rsign {R : Type*} [LinearOrder R] [Zero R] (x : R) : RSign :=
  if x < 0 then .neg else if x = 0 then .zero else .pos

lemma rsign_neg_iff {R : Type*} [LinearOrder R] [Zero R] {x : R} :
    rsign x = .neg ↔ x < 0 := by
  unfold rsign; split_ifs with h1 h2 <;> simp_all

lemma rsign_zero_iff {R : Type*} [LinearOrder R] [Zero R] {x : R} :
    rsign x = .zero ↔ x = 0 := by
  unfold rsign; split_ifs with h1 h2 <;> simp_all [ne_of_lt]

lemma rsign_pos_iff {R : Type*} [LinearOrder R] [Zero R] {x : R} :
    rsign x = .pos ↔ 0 < x := by
  unfold rsign
  split_ifs with h1 h2
  · simp [not_lt.mpr (le_of_lt h1)]
  · subst h2; simp
  · exact ⟨fun _ => lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2), fun _ => rfl⟩

lemma rsign_neg {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] (x : R) :
    rsign (-x) = (rsign x).negate := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [rsign_neg_iff.mpr h, rsign_pos_iff.mpr (neg_pos.mpr h)]; rfl
  · simp [rsign_zero_iff.mpr rfl, RSign.negate]
  · rw [rsign_pos_iff.mpr h, rsign_neg_iff.mpr (neg_lt_zero.mpr h)]; rfl

lemma rsign_mul_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {c x : R} (hc : 0 < c) : rsign (c * x) = rsign x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [rsign_neg_iff.mpr h, rsign_neg_iff.mpr (mul_neg_of_pos_of_neg hc h)]
  · simp [rsign_zero_iff.mpr rfl]
  · rw [rsign_pos_iff.mpr h, rsign_pos_iff.mpr (mul_pos hc h)]

lemma rsign_mul_neg {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {c x : R} (hc : c < 0) : rsign (c * x) = (rsign x).negate := by
  have : c * x = -((-c) * x) := by ring
  rw [this, rsign_neg, rsign_mul_pos (neg_pos.mpr hc)]

lemma rsign_real_hom {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (ι : ℝ →+* R) (r : ℝ) : rsign (ι r) = rsign r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · have hpos : 0 < -r := neg_pos.mpr h
    have hsq : -r = (Real.sqrt (-r)) ^ 2 := (Real.sq_sqrt (le_of_lt hpos)).symm
    have hι : 0 < ι (-r) := by
      rw [hsq, map_pow]
      have hne : ι (Real.sqrt (-r)) ≠ 0 := by
        intro h0
        have := ι.injective (h0.trans (map_zero ι).symm)
        linarith [Real.sqrt_pos.mpr hpos]
      exact sq_pos_of_ne_zero hne
    rw [map_neg] at hι
    rw [rsign_neg_iff.mpr h, rsign_neg_iff.mpr (by linarith)]
  · rw [map_zero, rsign_zero_iff.mpr rfl, rsign_zero_iff.mpr rfl]
  · have hsq : r = (Real.sqrt r) ^ 2 := (Real.sq_sqrt (le_of_lt h)).symm
    have hι : 0 < ι r := by
      rw [hsq, map_pow]
      have hne : ι (Real.sqrt r) ≠ 0 := by
        intro h0
        have := ι.injective (h0.trans (map_zero ι).symm)
        linarith [Real.sqrt_pos.mpr h]
      exact sq_pos_of_ne_zero hne
    rw [rsign_pos_iff.mpr h, rsign_pos_iff.mpr hι]

/-! #### Univariate calculus over `HasPolyIVT` -/

lemma HasPolyIVT.ivt_both {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasPolyIVT R] {p : Polynomial R} {a b : R} (hab : a < b)
    (hprod : p.eval a * p.eval b < 0) :
    ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0 := by
  rcases mul_neg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt (-p) a b hab (by simpa using ha) (by simpa using hb)
    exact ⟨c, hc1, hc2, by simpa using hce⟩
  · exact HasPolyIVT.ivt p a b hab ha hb

lemma HasPolyIVT.const_sign_of_no_roots {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [HasPolyIVT R] {p : Polynomial R} {a b : R}
    (hno : ∀ c, a < c → c < b → p.eval c ≠ 0)
    {x y : R} (hx1 : a < x) (hx2 : x < b) (hy1 : a < y) (hy2 : y < b) :
    rsign (p.eval x) = rsign (p.eval y) := by
  have hx0 : p.eval x ≠ 0 := hno x hx1 hx2
  have hy0 : p.eval y ≠ 0 := hno y hy1 hy2
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · by_contra hne
    have hprod : p.eval x * p.eval y < 0 := by
      rcases lt_or_gt_of_ne hx0 with hx | hx <;> rcases lt_or_gt_of_ne hy0 with hy | hy
      · exact absurd ((rsign_neg_iff.mpr hx).trans (rsign_neg_iff.mpr hy).symm) hne
      · exact mul_neg_of_neg_of_pos hx hy
      · exact mul_neg_of_pos_of_neg hx hy
      · exact absurd ((rsign_pos_iff.mpr hx).trans (rsign_pos_iff.mpr hy).symm) hne
    obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hxy hprod
    exact hno c (lt_trans hx1 hc1) (lt_trans hc2 hy2) hce
  · rfl
  · by_contra hne
    have hprod : p.eval y * p.eval x < 0 := by
      rcases lt_or_gt_of_ne hy0 with hy | hy <;> rcases lt_or_gt_of_ne hx0 with hx | hx
      · exact absurd ((rsign_neg_iff.mpr hx).trans (rsign_neg_iff.mpr hy).symm) hne
      · exact mul_neg_of_neg_of_pos hy hx
      · exact mul_neg_of_pos_of_neg hy hx
      · exact absurd ((rsign_pos_iff.mpr hx).trans (rsign_pos_iff.mpr hy).symm) hne
    obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hyx hprod
    exact hno c (lt_trans hy1 hc1) (lt_trans hc2 hx2) hce

lemma HasPolyIVT.rolle {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasPolyIVT R] (p : Polynomial R) {a b : R} (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c : R, a < c ∧ c < b ∧ p.derivative.eval c = 0 := by
  let q : Polynomial R := p - Polynomial.C (p.eval a)
  have hqa : q.eval a = 0 := by simp [q]
  have hqb : q.eval b = 0 := by simp [q, heq]
  have hqder : q.derivative = p.derivative := by simp [q]
  by_cases hq0 : q = 0
  · refine ⟨(a + b) / 2, by linarith, by linarith, ?_⟩
    rw [← hqder, hq0]; simp
  · classical
    let S : Finset R := q.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)
    have hbS : b ∈ S := by
      simp only [S, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hq0,
        Polynomial.IsRoot]
      exact ⟨hqb, hab, le_rfl⟩
    let b' : R := S.min' ⟨b, hbS⟩
    have hb'S : b' ∈ S := Finset.min'_mem S ⟨b, hbS⟩
    have hb'1 : a < b' := (Finset.mem_filter.mp hb'S).2.1
    have hb'2 : b' ≤ b := (Finset.mem_filter.mp hb'S).2.2
    have hqb' : q.eval b' = 0 :=
      (Polynomial.mem_roots hq0).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hb'S).1)
    have hno_root : ∀ r : R, a < r → r < b' → q.eval r ≠ 0 := by
      intro r hr1 hr2 hqr
      have hrS : r ∈ S := by
        simp only [S, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hq0,
          Polynomial.IsRoot]
        exact ⟨hqr, hr1, le_trans (le_of_lt hr2) hb'2⟩
      exact not_lt.mpr (Finset.min'_le S r hrS) hr2
    obtain ⟨q1, hq1_eq, hq1_ndvd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq0 a
    set k := q.rootMultiplicity a
    have hk_pos : 0 < k := (Polynomial.rootMultiplicity_pos hq0).mpr hqa
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk_pos)
    have hq1_ne : q1 ≠ 0 := by rintro rfl; simp at hq1_eq; exact hq0 hq1_eq
    have hq1_a : q1.eval a ≠ 0 := fun ha0 => hq1_ndvd (Polynomial.dvd_iff_isRoot.mpr ha0)
    have hq1_b' : q1.eval b' = 0 := by
      have h1 := congr_arg (Polynomial.eval b') hq1_eq
      simp only [hqb', Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt hb'1)))
    obtain ⟨h, hh_eq, hh_ndvd⟩ := q1.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq1_ne b'
    set l := q1.rootMultiplicity b'
    have hl_pos : 0 < l := (Polynomial.rootMultiplicity_pos hq1_ne).mpr hq1_b'
    obtain ⟨l', hl'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hl_pos)
    have hh_b' : h.eval b' ≠ 0 := fun hb0 => hh_ndvd (Polynomial.dvd_iff_isRoot.mpr hb0)
    have hh_a : h.eval a ≠ 0 := by
      intro ha0
      apply hq1_a
      rw [hh_eq, Polynomial.eval_mul, ha0, mul_zero]
    have hh_same : 0 < h.eval a * h.eval b' := by
      by_contra hle
      have hneg : h.eval a * h.eval b' < 0 :=
        lt_of_le_of_ne (not_lt.mp hle) (mul_ne_zero hh_a hh_b')
      obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hb'1 hneg
      apply hno_root c hc1 hc2
      rw [hq1_eq, hh_eq]
      simp [hce]
    let g : Polynomial R :=
      Polynomial.C ((k' + 1 : ℕ) : R) * (Polynomial.X - Polynomial.C b') * h +
      Polynomial.C ((l' + 1 : ℕ) : R) * (Polynomial.X - Polynomial.C a) * h +
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b') * h.derivative
    have hq_fact : q = (Polynomial.X - Polynomial.C a) ^ (k' + 1) *
        ((Polynomial.X - Polynomial.C b') ^ (l' + 1) * h) := by
      rw [hq1_eq, hh_eq, hk', hl']
    have hder_eq : q.derivative =
        (Polynomial.X - Polynomial.C a) ^ k' * (Polynomial.X - Polynomial.C b') ^ l' * g := by
      rw [hq_fact]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
        Nat.add_sub_cancel, g]
      ring
    have hga : g.eval a = ((k' + 1 : ℕ) : R) * (a - b') * h.eval a := by
      simp [g]
    have hgb' : g.eval b' = ((l' + 1 : ℕ) : R) * (b' - a) * h.eval b' := by
      simp [g]
    have hg_prod : g.eval a * g.eval b' < 0 := by
      rw [hga, hgb']
      have hk1 : (0 : R) < ((k' + 1 : ℕ) : R) := by positivity
      have hl1 : (0 : R) < ((l' + 1 : ℕ) : R) := by positivity
      have hba : (0 : R) < b' - a := sub_pos.mpr hb'1
      have hid : ((k' + 1 : ℕ) : R) * (a - b') * h.eval a *
          (((l' + 1 : ℕ) : R) * (b' - a) * h.eval b') =
          -(((k' + 1 : ℕ) : R) * ((l' + 1 : ℕ) : R) * (b' - a) ^ 2 * (h.eval a * h.eval b')) := by
        ring
      rw [hid]
      exact neg_lt_zero.mpr (by positivity)
    obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hb'1 hg_prod
    refine ⟨c, hc1, lt_of_lt_of_le hc2 hb'2, ?_⟩
    rw [← hqder, hder_eq]
    simp [hce]

lemma HasPolyIVT.mvt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasPolyIVT R] (p : Polynomial R) {a b : R} (hab : a < b) :
    ∃ c : R, a < c ∧ c < b ∧ p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  let q : Polynomial R := Polynomial.C (b - a) * p - Polynomial.C (p.eval b - p.eval a) * Polynomial.X
  have heq : q.eval a = q.eval b := by simp [q]; ring
  obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.rolle q hab heq
  refine ⟨c, hc1, hc2, ?_⟩
  have hder : q.derivative.eval c = (b - a) * p.derivative.eval c - (p.eval b - p.eval a) := by
    simp [q]
  rw [hder] at hce
  linear_combination -hce

noncomputable def signAtPosInf {R : Type*} [Field R] [LinearOrder R] (p : Polynomial R) : RSign :=
  rsign p.leadingCoeff

noncomputable def signAtNegInf {R : Type*} [Field R] [LinearOrder R] (p : Polynomial R) : RSign :=
  if Even p.natDegree then rsign p.leadingCoeff else (rsign p.leadingCoeff).negate

lemma exists_sign_at_inf {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Polynomial R) (hp : p ≠ 0) :
    ∃ M : R, 0 < M ∧
      (∀ x : R, M < x → rsign (p.eval x) = signAtPosInf p) ∧
      (∀ x : R, x < -M → rsign (p.eval x) = signAtNegInf p) := by
  let d := p.natDegree
  let lc := p.leadingCoeff
  have hlc : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hlc_pos : 0 < |lc| := abs_pos.mpr hlc
  let S : R := ∑ i ∈ Finset.range d, |p.coeff i|
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let M : R := 1 + S / |lc|
  have hM_ge1 : 1 ≤ M := by dsimp [M]; have : 0 ≤ S / |lc| := div_nonneg hS_nn (le_of_lt hlc_pos); linarith
  have htail : ∀ x : R, M < |x| →
      |∑ i ∈ Finset.range d, p.coeff i * x ^ i| < |lc * x ^ d| := by
    intro x hx
    have hx_ge1 : 1 ≤ |x| := le_trans hM_ge1 (le_of_lt hx)
    have hsum_le : |∑ i ∈ Finset.range d, p.coeff i * x ^ i| ≤ S * |x| ^ (d - 1) := by
      calc |∑ i ∈ Finset.range d, p.coeff i * x ^ i|
          ≤ ∑ i ∈ Finset.range d, |p.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range d, |p.coeff i| * |x| ^ i := by
            congr 1; ext i; rw [abs_mul, abs_pow]
        _ ≤ ∑ i ∈ Finset.range d, |p.coeff i| * |x| ^ (d - 1) := by
            apply Finset.sum_le_sum; intro i hi
            rw [Finset.mem_range] at hi
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx_ge1 (by omega)) (abs_nonneg _)
        _ = S * |x| ^ (d - 1) := by rw [← Finset.sum_mul]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · have : S = 0 := by simp [S, hd0]
      rw [this, zero_mul] at hsum_le
      have hpos : 0 < |lc * x ^ d| := by rw [hd0, pow_zero, mul_one]; exact hlc_pos
      linarith
    · have hS_lt : S < |lc| * |x| := by
        have h1 : S / |lc| < |x| := by dsimp [M] at hx; linarith
        exact mul_comm |x| |lc| ▸ (div_lt_iff₀ hlc_pos).mp h1
      have hpow_pos : 0 < |x| ^ (d - 1) := pow_pos (lt_of_lt_of_le zero_lt_one hx_ge1) _
      have hmul : S * |x| ^ (d - 1) < |lc| * |x| * |x| ^ (d - 1) :=
        mul_lt_mul_of_pos_right hS_lt hpow_pos
      have heq : |lc| * |x| * |x| ^ (d - 1) = |lc * x ^ d| := by
        rw [abs_mul, abs_pow, mul_assoc, ← pow_succ', Nat.sub_add_cancel hdpos]
      linarith
  have heval_split : ∀ x : R,
      p.eval x = (∑ i ∈ Finset.range d, p.coeff i * x ^ i) + lc * x ^ d := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
    rfl
  have hsame : ∀ x : R, M < |x| → rsign (p.eval x) = rsign (lc * x ^ d) := by
    intro x hx
    have hlt := htail x hx
    rw [heval_split x]
    have hx_ne : x ≠ 0 := by intro hx0; rw [hx0, abs_zero] at hx; linarith
    rcases lt_or_gt_of_ne (mul_ne_zero hlc (pow_ne_zero d hx_ne)) with hneg | hpos
    · rw [abs_of_neg hneg] at hlt
      have h1 := le_of_abs_le (le_of_lt hlt)
      have hsum_neg : (∑ i ∈ Finset.range d, p.coeff i * x ^ i) + lc * x ^ d < 0 := by
        have := (abs_lt.mp hlt).2; linarith
      rw [rsign_neg_iff.mpr hsum_neg, rsign_neg_iff.mpr hneg]
    · rw [abs_of_pos hpos] at hlt
      have hsum_pos : 0 < (∑ i ∈ Finset.range d, p.coeff i * x ^ i) + lc * x ^ d := by
        have := (abs_lt.mp hlt).1; linarith
      rw [rsign_pos_iff.mpr hsum_pos, rsign_pos_iff.mpr hpos]
  refine ⟨M, by linarith, ?_, ?_⟩
  · intro x hx
    have habs : M < |x| := by rw [abs_of_pos (by linarith)]; exact hx
    rw [hsame x habs, mul_comm, rsign_mul_pos (pow_pos (by linarith) d)]
    rfl
  · intro x hx
    have habs : M < |x| := by rw [abs_of_neg (by linarith)]; linarith
    rw [hsame x habs, mul_comm]
    dsimp [signAtNegInf, d, lc]
    split_ifs with heven
    · obtain ⟨k, hk⟩ := heven
      have hpow : 0 < x ^ p.natDegree := by
        rw [hk, ← two_mul, pow_mul]; exact pow_pos (sq_pos_of_neg (by linarith)) k
      exact rsign_mul_pos hpow
    · have hodd : Odd p.natDegree := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hpow : x ^ p.natDegree < 0 := by
        rw [hk, pow_succ, pow_mul]
        exact mul_neg_of_pos_of_neg (pow_pos (sq_pos_of_neg (by linarith)) k) (by linarith)
      exact rsign_mul_neg hpow

/-! #### Truncation and even-power formal pseudo-division in `Polynomial A` -/

noncomputable def truncPoly {A : Type*} [CommRing A] (q : Polynomial A) (k : ℕ) : Polynomial A :=
  ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (q.coeff i)

lemma coeff_truncPoly {A : Type*} [CommRing A] (q : Polynomial A) (k i : ℕ) :
    (truncPoly q k).coeff i = if i ≤ k then q.coeff i else 0 := by
  unfold truncPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hi : i ≤ k
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hi'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) hi'
  · rw [if_neg hi, Finset.sum_eq_zero]
    intro b hb
    rw [Finset.mem_range] at hb
    rw [if_neg (by omega)]

lemma natDegree_truncPoly_le {A : Type*} [CommRing A] (q : Polynomial A) (k : ℕ) :
    (truncPoly q k).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_truncPoly, if_neg (by omega)]

lemma map_truncPoly_eq {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (q : Polynomial A) (k : ℕ) (hdeg : (q.map φ).natDegree ≤ k) :
    (truncPoly q k).map φ = q.map φ := by
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_truncPoly]
  split_ifs with hi
  · rfl
  · rw [map_zero]
    symm
    have := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp hi))
    simpa [Polynomial.coeff_map] using this

noncomputable def pseudoRemAux {A : Type*} [CommRing A] (q : Polynomial A) (k : ℕ) :
    ℕ → Polynomial A → Polynomial A
  | 0, r => r
  | m + 1, r =>
    if m + 1 < k then r
    else
      let c := q.coeff k
      let r' := Polynomial.C (c ^ 2) * r -
        Polynomial.C (c * r.coeff (m + 1)) * Polynomial.X ^ (m + 1 - k) * q
      pseudoRemAux q k m r'

noncomputable def pseudoRem {A : Type*} [CommRing A] (p q : Polynomial A) (k : ℕ) : Polynomial A :=
  pseudoRemAux q k p.natDegree p

lemma pseudoRemAux_spec {A : Type*} [CommRing A] (q : Polynomial A) (k : ℕ)
    (hk : 1 ≤ k) (hq : q.natDegree ≤ k) :
    ∀ (m : ℕ) (r : Polynomial A), r.natDegree ≤ m →
      (pseudoRemAux q k m r).natDegree < k ∧
      ∃ (e : ℕ) (U : Polynomial A),
        Polynomial.C ((q.coeff k) ^ (2 * e)) * r = U * q + pseudoRemAux q k m r := by
  intro m
  induction m with
  | zero =>
    intro r hr
    unfold pseudoRemAux
    refine ⟨by omega, 0, 0, by simp⟩
  | succ m ih =>
    intro r hr
    unfold pseudoRemAux
    split_ifs with hlt
    · exact ⟨by omega, 0, 0, by simp⟩
    · set c := q.coeff k
      set r' := Polynomial.C (c ^ 2) * r -
        Polynomial.C (c * r.coeff (m + 1)) * Polynomial.X ^ (m + 1 - k) * q
      have hr'_deg : r'.natDegree ≤ m := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro j hj
        dsimp [r']
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow_mul']
        split_ifs with hjk
        · by_cases hjm : j = m + 1
          · subst hjm
            have hsub : m + 1 - (m + 1 - k) = k := by omega
            rw [hsub]
            change c ^ 2 * r.coeff (m + 1) - c * r.coeff (m + 1) * c = 0
            ring
          · have hgt : m + 1 < j := by omega
            have hr0 : r.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            have hq0 : q.coeff (j - (m + 1 - k)) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            rw [hr0, hq0]; ring
        · have hr0 : r.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [hr0]; ring
      obtain ⟨hdeg', e, U, hEq⟩ := ih r' hr'_deg
      refine ⟨hdeg', e + 1,
        U + Polynomial.C (c ^ (2 * e) * (c * r.coeff (m + 1))) * Polynomial.X ^ (m + 1 - k), ?_⟩
      have hpow : Polynomial.C (c ^ (2 * (e + 1))) = Polynomial.C (c ^ (2 * e)) * Polynomial.C (c ^ 2) := by
        rw [← map_mul, ← pow_add, show 2 * (e + 1) = 2 * e + 2 by omega]
      have hmul : Polynomial.C (c ^ (2 * e) * (c * r.coeff (m + 1))) =
          Polynomial.C (c ^ (2 * e)) * Polynomial.C (c * r.coeff (m + 1)) := map_mul _ _ _
      rw [hpow, hmul]
      dsimp [r'] at hEq
      linear_combination hEq

lemma pseudoRem_spec {A : Type*} [CommRing A] (p q : Polynomial A) (k : ℕ)
    (hk : 1 ≤ k) (hq : q.natDegree ≤ k) :
    (pseudoRem p q k).natDegree < k ∧
    ∃ (e : ℕ) (U : Polynomial A),
      Polynomial.C ((q.coeff k) ^ (2 * e)) * p = U * q + pseudoRem p q k :=
  pseudoRemAux_spec q k hk hq p.natDegree p le_rfl

lemma rsign_eval_pseudoRem {A R : Type*} [CommRing A] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (φ : A →+* R) (p q : Polynomial A) (k : ℕ)
    (hk : 1 ≤ k) (hq : q.natDegree ≤ k) (hc : φ (q.coeff k) ≠ 0)
    (x : R) (hx : (q.map φ).eval x = 0) :
    rsign ((p.map φ).eval x) = rsign (((pseudoRem p q k).map φ).eval x) := by
  obtain ⟨_, e, U, hEq⟩ := pseudoRem_spec p q k hk hq
  have hmap := congr_arg (fun f => (f.map φ).eval x) hEq
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow,
    hx, mul_zero, zero_add, map_pow] at hmap
  have hpow_pos : 0 < φ (q.coeff k) ^ (2 * e) := by
    rw [pow_mul]; exact pow_pos (sq_pos_of_ne_zero hc) e
  rw [← hmap, rsign_mul_pos hpow_pos]

/-! #### Root lists, open cells, and `SameSignTable` -/

noncomputable def rootList {R : Type*} [Field R] [LinearOrder R]
    (S : Finset (Polynomial R)) : List R :=
  letI : DecidableEq R := Classical.decEq R
  (S.biUnion fun p => if p = 0 then ∅ else p.roots.toFinset).sort (· ≤ ·)

lemma rootList_pairwise {R : Type*} [Field R] [LinearOrder R]
    (S : Finset (Polynomial R)) : (rootList S).Pairwise (· < ·) := by
  unfold rootList
  let : DecidableEq R := Classical.decEq R
  let T := S.biUnion fun p => if p = 0 then ∅ else p.roots.toFinset
  have hle := Finset.pairwise_sort T (· ≤ ·)
  have hnd := Finset.sort_nodup T (· ≤ ·)
  suffices ∀ {l : List R}, l.Pairwise (· ≤ ·) → l.Pairwise (· ≠ ·) → l.Pairwise (· < ·) from
    this hle hnd
  intro l h1 h2
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at h1 h2 ⊢
    exact ⟨fun b hb => lt_of_le_of_ne (h1.1 b hb) (h2.1 b hb), ih h1.2 h2.2⟩

lemma mem_rootList {R : Type*} [Field R] [LinearOrder R]
    (S : Finset (Polynomial R)) (x : R) :
    x ∈ rootList S ↔ ∃ p ∈ S, p ≠ 0 ∧ p.eval x = 0 := by
  unfold rootList
  let : DecidableEq R := Classical.decEq R
  rw [Finset.mem_sort, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    split_ifs at hx with hp0
    · simp at hx
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0] at hx
      exact ⟨p, hp, hp0, hx⟩
  · rintro ⟨p, hp, hp0, hpx⟩
    refine ⟨p, hp, ?_⟩
    rw [if_neg hp0, Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hpx

lemma list_eq_of_pairwise_lt_of_mem_iff {R : Type*} [LinearOrder R]
    {l1 l2 : List R} (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b bs => exact absurd ((hmem b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a as ih =>
    cases l2 with
    | nil => exact absurd ((hmem a).mp (List.mem_cons_self ..)) (by simp)
    | cons b bs =>
      have hab : a = b := by
        have ha : a ∈ b :: bs := (hmem a).mp (List.mem_cons_self ..)
        have hb : b ∈ a :: as := (hmem b).mpr (List.mem_cons_self ..)
        rcases List.mem_cons.mp ha with rfl | ha'
        · rfl
        · rcases List.mem_cons.mp hb with rfl | hb'
          · rfl
          · have hlt1 : b < a := (List.pairwise_cons.mp h2).1 a ha'
            have hlt2 : a < b := (List.pairwise_cons.mp h1).1 b hb'
            exact absurd (lt_trans hlt1 hlt2) (lt_irrefl b)
      subst hab
      congr 1
      apply ih (List.pairwise_cons.mp h1).2 (List.pairwise_cons.mp h2).2
      intro x
      constructor
      · intro hx
        have hxne : x ≠ a := ne_of_gt ((List.pairwise_cons.mp h1).1 x hx)
        exact (List.mem_cons.mp ((hmem x).mp (List.mem_cons_of_mem _ hx))).resolve_left hxne
      · intro hx
        have hxne : x ≠ a := ne_of_gt ((List.pairwise_cons.mp h2).1 x hx)
        exact (List.mem_cons.mp ((hmem x).mpr (List.mem_cons_of_mem _ hx))).resolve_left hxne

def inCell {R : Type*} [LinearOrder R] (rs : List R) (j : ℕ) (x : R) : Prop :=
  (∀ (_ : 0 < j) (h2 : j - 1 < rs.length), rs[j - 1]'h2 < x) ∧
  (∀ (h3 : j < rs.length), x < rs[j]'h3)

lemma pairwise_lt_get {R : Type*} [LinearOrder R] {rs : List R} (hrs : rs.Pairwise (· < ·))
    {i j : ℕ} (hi : i < rs.length) (hj : j < rs.length) (hij : i < j) :
    rs[i]'hi < rs[j]'hj :=
  List.pairwise_iff_getElem.mp hrs i j hi hj hij

lemma exists_inCell {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {rs : List R} (hrs : rs.Pairwise (· < ·)) {j : ℕ} (hj : j ≤ rs.length) :
    ∃ x : R, inCell rs j x := by
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hlen : 0 < rs.length
    · refine ⟨rs[0]'hlen - 1, fun h => absurd h (lt_irrefl 0), fun h => by linarith⟩
    · refine ⟨0, fun h => absurd h (lt_irrefl 0), fun h => absurd h hlen⟩
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjm : j - 1 < rs.length := by omega
    by_cases hjlt : j < rs.length
    · have hlt : rs[j - 1]'hjm < rs[j]'hjlt := pairwise_lt_get hrs hjm hjlt (by omega)
      refine ⟨(rs[j - 1]'hjm + rs[j]'hjlt) / 2, fun _ _ => by linarith, fun _ => by linarith⟩
    · refine ⟨rs[j - 1]'hjm + 1, fun _ _ => by linarith, fun h => absurd h hjlt⟩

lemma point_position {R : Type*} [LinearOrder R] {rs : List R} (hrs : rs.Pairwise (· < ·))
    (x : R) :
    (∃ (i : ℕ) (hi : i < rs.length), x = rs[i]'hi) ∨
    (∃ j, j ≤ rs.length ∧ inCell rs j x) := by
  by_cases hx : x ∈ rs
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact Or.inl ⟨i, hi, rfl⟩
  · right
    classical
    -- Count how many elements of rs are < x
    let j : ℕ := (rs.filter (fun r => decide (r < x))).length
    -- Actually prove by induction on rs!
    clear j
    induction rs with
    | nil => exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl 0), fun h => by simp at h⟩
    | cons a as ih =>
      have ha_ne : x ≠ a := fun h => hx (h ▸ List.mem_cons_self ..)
      have hx_as : x ∉ as := fun h => hx (List.mem_cons_of_mem _ h)
      rcases lt_or_gt_of_ne ha_ne with hxa | hax
      · refine ⟨0, Nat.zero_le _, fun h => absurd h (lt_irrefl 0), fun _ => by simpa using hxa⟩
      · obtain ⟨j, hj, hcell⟩ := ih (List.pairwise_cons.mp hrs).2 hx_as
        refine ⟨j + 1, by simp [hj], ?_, ?_⟩
        · intro _ h2
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · simpa using hax
          · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
            have hlt := hcell.1 (Nat.succ_pos j') (by simp at h2; omega)
            simpa using hlt
        · intro h3
          exact hcell.2 (by simpa using h3)

lemma no_root_inCell {R : Type*} [Field R] [LinearOrder R]
    {S : Finset (Polynomial R)} {p : Polynomial R} (hp : p ∈ S) (hp0 : p ≠ 0)
    {j : ℕ} (hj : j ≤ (rootList S).length) {x : R} (hx : inCell (rootList S) j x) :
    p.eval x ≠ 0 := by
  intro hpx
  have hmem : x ∈ rootList S := (mem_rootList S x).mpr ⟨p, hp, hp0, hpx⟩
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hmem
  rcases lt_or_ge i j with hij | hji
  · have hlt := hx.1 (by omega) (by omega)
    have hle : (rootList S)[i]'hi ≤ (rootList S)[j - 1]'(by omega) := by
      rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hij) with heq | hlt'
      · subst heq; exact le_rfl
      · exact le_of_lt (pairwise_lt_get (rootList_pairwise S) hi (by omega) hlt')
    exact not_lt.mpr hle (hxi ▸ hlt)
  · have hlt := hx.2 (by omega)
    have hle : (rootList S)[j]'(by omega) ≤ (rootList S)[i]'hi := by
      rcases eq_or_lt_of_le hji with rfl | hlt'
      · exact le_rfl
      · exact le_of_lt (pairwise_lt_get (rootList_pairwise S) (by omega) hi hlt')
    exact not_lt.mpr hle (hxi.symm ▸ hlt)

lemma const_sign_inCell {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasPolyIVT R] {S : Finset (Polynomial R)} {p : Polynomial R} (hp : p ∈ S)
    {j : ℕ} (hj : j ≤ (rootList S).length) {x y : R}
    (hx : inCell (rootList S) j x) (hy : inCell (rootList S) j y) :
    rsign (p.eval x) = rsign (p.eval y) := by
  by_cases hp0 : p = 0
  · subst hp0; simp
  · have hno : ∀ c : R, min x y - 1 < c → c < max x y + 1 →
        (min x y ≤ c ∧ c ≤ max x y → p.eval c ≠ 0) := by
      intro c _ _ ⟨hc1, hc2⟩
      apply no_root_inCell hp hp0 hj
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · exact lt_of_lt_of_le (lt_min (hx.1 h1 h2) (hy.1 h1 h2)) hc1
      · exact lt_of_le_of_lt hc2 (max_lt (hx.2 h3) (hy.2 h3))
    have hno' : ∀ c : R, min x y < c → c < max x y → p.eval c ≠ 0 := fun c hc1 hc2 =>
      hno c (by linarith) (by linarith) ⟨le_of_lt hc1, le_of_lt hc2⟩
    have hx0 : p.eval x ≠ 0 := no_root_inCell hp hp0 hj hx
    have hy0 : p.eval y ≠ 0 := no_root_inCell hp hp0 hj hy
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · by_contra hne
      have hprod : p.eval x * p.eval y < 0 := by
        rcases lt_or_gt_of_ne hx0 with h1 | h1 <;> rcases lt_or_gt_of_ne hy0 with h2 | h2
        · exact absurd ((rsign_neg_iff.mpr h1).trans (rsign_neg_iff.mpr h2).symm) hne
        · exact mul_neg_of_neg_of_pos h1 h2
        · exact mul_neg_of_pos_of_neg h1 h2
        · exact absurd ((rsign_pos_iff.mpr h1).trans (rsign_pos_iff.mpr h2).symm) hne
      obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hxy hprod
      exact hno' c (by rw [min_eq_left (le_of_lt hxy)]; exact hc1)
        (by rw [max_eq_right (le_of_lt hxy)]; exact hc2) hce
    · rfl
    · by_contra hne
      have hprod : p.eval y * p.eval x < 0 := by
        rcases lt_or_gt_of_ne hy0 with h2 | h2 <;> rcases lt_or_gt_of_ne hx0 with h1 | h1
        · exact absurd ((rsign_neg_iff.mpr h1).trans (rsign_neg_iff.mpr h2).symm) hne
        · exact mul_neg_of_neg_of_pos h2 h1
        · exact mul_neg_of_pos_of_neg h2 h1
        · exact absurd ((rsign_pos_iff.mpr h1).trans (rsign_pos_iff.mpr h2).symm) hne
      obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.ivt_both hyx hprod
      exact hno' c (by rw [min_eq_right (le_of_lt hyx)]; exact hc1)
        (by rw [max_eq_left (le_of_lt hyx)]; exact hc2) hce

/-- Complete sign table equivalence for a finite set `F ⊆ A[X]` specialized via `φ₁ : A →+* R₁`
and `φ₂ : A →+* R₂`. -/
structure SameSignTable {A R₁ R₂ : Type*} [CommRing A]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂]
    (F : Finset (Polynomial A)) (φ₁ : A →+* R₁) (φ₂ : A →+* R₂) : Prop where
  len_eq : (rootList (F.image (Polynomial.map φ₁))).length =
           (rootList (F.image (Polynomial.map φ₂))).length
  at_roots : ∀ (i : ℕ) (h1 : i < (rootList (F.image (Polynomial.map φ₁))).length)
      (h2 : i < (rootList (F.image (Polynomial.map φ₂))).length),
      ∀ p ∈ F,
        rsign ((p.map φ₁).eval ((rootList (F.image (Polynomial.map φ₁)))[i]'h1)) =
        rsign ((p.map φ₂).eval ((rootList (F.image (Polynomial.map φ₂)))[i]'h2))
  at_cells : ∀ (j : ℕ), j ≤ (rootList (F.image (Polynomial.map φ₁))).length →
      ∀ (x1 : R₁) (x2 : R₂),
        inCell (rootList (F.image (Polynomial.map φ₁))) j x1 →
        inCell (rootList (F.image (Polynomial.map φ₂))) j x2 →
        ∀ p ∈ F, rsign ((p.map φ₁).eval x1) = rsign ((p.map φ₂).eval x2)

lemma SameSignTable.realize {A R₁ R₂ : Type*} [CommRing A]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂]
    {F : Finset (Polynomial A)} {φ₁ : A →+* R₁} {φ₂ : A →+* R₂}
    (hST : SameSignTable F φ₁ φ₂) (t2 : R₂) :
    ∃ t1 : R₁, ∀ p ∈ F, rsign ((p.map φ₁).eval t1) = rsign ((p.map φ₂).eval t2) := by
  let rs1 := rootList (F.image (Polynomial.map φ₁))
  let rs2 := rootList (F.image (Polynomial.map φ₂))
  rcases point_position (rootList_pairwise (F.image (Polynomial.map φ₂))) t2 with
    ⟨i, hi, rfl⟩ | ⟨j, hj, hcell⟩
  · have hi1 : i < rs1.length := hST.len_eq.symm ▸ hi
    exact ⟨rs1[i]'hi1, hST.at_roots i hi1 hi⟩
  · have hj1 : j ≤ rs1.length := hST.len_eq.symm ▸ hj
    obtain ⟨t1, ht1⟩ := exists_inCell (rootList_pairwise (F.image (Polynomial.map φ₁))) hj1
    exact ⟨t1, hST.at_cells j hj1 t1 t2 ht1 hcell⟩

lemma SameSignTable.map_eq_zero_iff {A R₁ R₂ : Type*} [CommRing A]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂]
    {F : Finset (Polynomial A)} {φ₁ : A →+* R₁} {φ₂ : A →+* R₂}
    (hST : SameSignTable F φ₁ φ₂) {p : Polynomial A} (hp : p ∈ F) :
    p.map φ₁ = 0 ↔ p.map φ₂ = 0 := by
  obtain ⟨x1, hx1⟩ := exists_inCell (rootList_pairwise (F.image (Polynomial.map φ₁))) (Nat.zero_le _)
  obtain ⟨x2, hx2⟩ := exists_inCell (rootList_pairwise (F.image (Polynomial.map φ₂))) (Nat.zero_le _)
  have hsign := hST.at_cells 0 (Nat.zero_le _) x1 x2 hx1 hx2 p hp
  have h1 : p.map φ₁ = 0 ↔ rsign ((p.map φ₁).eval x1) = .zero := by
    rw [rsign_zero_iff]
    constructor
    · intro h0; rw [h0, Polynomial.eval_zero]
    · intro hev; by_contra hne
      exact no_root_inCell (Finset.mem_image_of_mem _ hp) hne (Nat.zero_le _) hx1 hev
  have h2 : p.map φ₂ = 0 ↔ rsign ((p.map φ₂).eval x2) = .zero := by
    rw [rsign_zero_iff]
    constructor
    · intro h0; rw [h0, Polynomial.eval_zero]
    · intro hev; by_contra hne
      exact no_root_inCell (Finset.mem_image_of_mem _ hp) hne (Nat.zero_le _) hx2 hev
  rw [h1, h2, hsign]

lemma SameSignTable.mono {A R₁ R₂ : Type*} [CommRing A]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁] [HasPolyIVT R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂] [HasPolyIVT R₂]
    {F F' : Finset (Polynomial A)} {φ₁ : A →+* R₁} {φ₂ : A →+* R₂}
    (hsub : F ⊆ F') (hST : SameSignTable F' φ₁ φ₂) :
    SameSignTable F φ₁ φ₂ := by
  classical
  let rs1' := rootList (F'.image (Polynomial.map φ₁))
  let rs2' := rootList (F'.image (Polynomial.map φ₂))
  let L := rs1'.length
  have hL : rs2'.length = L := hST.len_eq.symm
  let keep : Fin L → Bool := fun i =>
    decide (∃ p ∈ F, p.map φ₁ ≠ 0 ∧ (p.map φ₁).eval (rs1'[i.val]'i.isLt) = 0)
  have hkeep_iff2 : ∀ i : Fin L, keep i = true ↔
      ∃ p ∈ F, p.map φ₂ ≠ 0 ∧ (p.map φ₂).eval (rs2'[i.val]'(hL.symm ▸ i.isLt)) = 0 := by
    intro i
    simp only [keep, decide_eq_true_eq]
    constructor <;> rintro ⟨p, hp, hne, hev⟩
    · refine ⟨p, hp, ?_, ?_⟩
      · exact mt (hST.map_eq_zero_iff (hsub hp)).mpr hne
      · rw [← rsign_zero_iff, ← hST.at_roots i.val i.isLt (hL.symm ▸ i.isLt) p (hsub hp),
          rsign_zero_iff]
        exact hev
    · refine ⟨p, hp, ?_, ?_⟩
      · exact mt (hST.map_eq_zero_iff (hsub hp)).mp hne
      · rw [← rsign_zero_iff, hST.at_roots i.val i.isLt (hL.symm ▸ i.isLt) p (hsub hp),
          rsign_zero_iff]
        exact hev
  let idxs : List (Fin L) := (List.finRange L).filter (fun i => keep i)
  have hidxs_pw : idxs.Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact List.pairwise_lt_finRange L
  let sub1 : List R₁ := idxs.map (fun i => rs1'[i.val]'i.isLt)
  let sub2 : List R₂ := idxs.map (fun i => rs2'[i.val]'(hL.symm ▸ i.isLt))
  have hsub1_pw : sub1.Pairwise (· < ·) :=
    (List.pairwise_map.mpr (hidxs_pw.imp fun h =>
      pairwise_lt_get (rootList_pairwise _) _ _ h))
  have hsub2_pw : sub2.Pairwise (· < ·) :=
    (List.pairwise_map.mpr (hidxs_pw.imp fun h =>
      pairwise_lt_get (rootList_pairwise _) _ _ h))
  have hsub1_eq : rootList (F.image (Polynomial.map φ₁)) = sub1 := by
    apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _) hsub1_pw
    intro x
    rw [mem_rootList]
    constructor
    · rintro ⟨_, hpm, hp0, hpx⟩
      obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hpm
      have hx' : x ∈ rs1' :=
        (mem_rootList _ x).mpr ⟨p.map φ₁, Finset.mem_image_of_mem _ (hsub hpF), hp0, hpx⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx'
      refine List.mem_map.mpr ⟨⟨i, hi⟩, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, decide_eq_true ⟨p, hpF, hp0, hpx⟩⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hki : keep i = true := (List.mem_filter.mp hi).2
      obtain ⟨p, hpF, hp0, hpx⟩ := of_decide_eq_true hki
      exact ⟨p.map φ₁, Finset.mem_image_of_mem _ hpF, hp0, hpx⟩
  have hsub2_eq : rootList (F.image (Polynomial.map φ₂)) = sub2 := by
    apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _) hsub2_pw
    intro x
    rw [mem_rootList]
    constructor
    · rintro ⟨_, hpm, hp0, hpx⟩
      obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hpm
      have hx' : x ∈ rs2' :=
        (mem_rootList _ x).mpr ⟨p.map φ₂, Finset.mem_image_of_mem _ (hsub hpF), hp0, hpx⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx'
      refine List.mem_map.mpr ⟨⟨i, hL ▸ hi⟩, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, (hkeep_iff2 ⟨i, hL ▸ hi⟩).mpr ⟨p, hpF, hp0, hpx⟩⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hki : keep i = true := (List.mem_filter.mp hi).2
      obtain ⟨p, hpF, hp0, hpx⟩ := (hkeep_iff2 i).mp hki
      exact ⟨p.map φ₂, Finset.mem_image_of_mem _ hpF, hp0, hpx⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hsub1_eq, hsub2_eq]; simp [sub1, sub2]
  · intro i h1 h2 p hp
    have h1' : i < idxs.length := by simpa [hsub1_eq, sub1] using h1
    have he1 : (rootList (F.image (Polynomial.map φ₁)))[i]'h1 =
        rs1'[(idxs[i]'h1').val]'(idxs[i]'h1').isLt := by
      simp [hsub1_eq, sub1]
    have he2 : (rootList (F.image (Polynomial.map φ₂)))[i]'h2 =
        rs2'[(idxs[i]'h1').val]'(hL.symm ▸ (idxs[i]'h1').isLt) := by
      simp [hsub2_eq, sub2]
    rw [he1, he2]
    exact hST.at_roots (idxs[i]'h1').val (idxs[i]'h1').isLt (hL.symm ▸ (idxs[i]'h1').isLt) p (hsub hp)
  · intro j hj x1 x2 hx1 hx2 p hp
    have hj' : j ≤ idxs.length := by simpa [hsub1_eq, sub1] using hj
    let j' : ℕ := if h : 0 < j then (idxs[j - 1]'(by omega)).val + 1 else 0
    have hj'L : j' ≤ L := by
      dsimp [j']; split_ifs with h
      · exact (idxs[j - 1]'(by omega)).isLt
      · exact Nat.zero_le L
    obtain ⟨x1', hx1'⟩ := exists_inCell (rootList_pairwise (F'.image (Polynomial.map φ₁))) hj'L
    obtain ⟨x2', hx2'⟩ := exists_inCell (rootList_pairwise (F'.image (Polynomial.map φ₂))) (hL.symm ▸ hj'L)
    have hx1'_in : inCell (rootList (F.image (Polynomial.map φ₁))) j x1' := by
      rw [hsub1_eq]
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · have h2' : j - 1 < idxs.length := by simpa [sub1] using h2
        have hjeq : j' = (idxs[j - 1]'h2').val + 1 := dif_pos h1
        have hjm1 : j' - 1 < (rootList (F'.image (Polynomial.map φ₁))).length := by
          have := (idxs[j - 1]'h2').isLt; change j' - 1 < L; omega
        have hlt := hx1'.1 (by omega) hjm1
        simpa [sub1, hjeq] using hlt
      · have h3' : j < idxs.length := by simpa [sub1] using h3
        have hj'le : j' ≤ (idxs[j]'h3').val := by
          dsimp [j']; split_ifs with h1
          · exact Nat.succ_le_of_lt (pairwise_lt_get hidxs_pw (by omega) h3' (by omega))
          · exact Nat.zero_le _
        have hj'lt : j' < (rootList (F'.image (Polynomial.map φ₁))).length :=
          lt_of_le_of_lt hj'le (idxs[j]'h3').isLt
        have hlt1 := hx1'.2 hj'lt
        have hle2 : rs1'[j']'hj'lt ≤ rs1'[(idxs[j]'h3').val]'(idxs[j]'h3').isLt := by
          rcases eq_or_lt_of_le hj'le with heq | hlt
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise _) _ _ hlt)
        simpa [sub1] using lt_of_lt_of_le hlt1 hle2
    have hx2'_in : inCell (rootList (F.image (Polynomial.map φ₂))) j x2' := by
      rw [hsub2_eq]
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · have h2' : j - 1 < idxs.length := by simpa [sub2] using h2
        have hjeq : j' = (idxs[j - 1]'h2').val + 1 := dif_pos h1
        have hjm1 : j' - 1 < (rootList (F'.image (Polynomial.map φ₂))).length := by
          have := (idxs[j - 1]'h2').isLt; change j' - 1 < rs2'.length; omega
        have hlt := hx2'.1 (by omega) hjm1
        simpa [sub2, hjeq] using hlt
      · have h3' : j < idxs.length := by simpa [sub2] using h3
        have hj'le : j' ≤ (idxs[j]'h3').val := by
          dsimp [j']; split_ifs with h1
          · exact Nat.succ_le_of_lt (pairwise_lt_get hidxs_pw (by omega) h3' (by omega))
          · exact Nat.zero_le _
        have hj'lt : j' < (rootList (F'.image (Polynomial.map φ₂))).length := by
          have := (idxs[j]'h3').isLt; change j' < rs2'.length; omega
        have hlt1 := hx2'.2 hj'lt
        have hle2 : rs2'[j']'hj'lt ≤
            rs2'[(idxs[j]'h3').val]'(hL.symm ▸ (idxs[j]'h3').isLt) := by
          rcases eq_or_lt_of_le hj'le with heq | hlt
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise _) _ _ hlt)
        simpa [sub2] using lt_of_lt_of_le hlt1 hle2
    have hc1 := const_sign_inCell (Finset.mem_image_of_mem _ hp) hj hx1 hx1'_in
    have hc2 := const_sign_inCell (Finset.mem_image_of_mem _ hp) (by rw [hsub2_eq]; simpa [sub2] using hj') hx2 hx2'_in
    rw [hc1, hc2]
    exact hST.at_cells j' hj'L x1' x2' hx1' hx2' p (hsub hp)

/-! #### Cell root dichotomy, `buildTags`, `SameSignTable.insert_poly`, and Hörmander's Lemma -/

lemma derivative_ne_zero_of_natDegree_pos {R : Type*} [Field R] [CharZero R]
    {P : Polynomial R} (hdeg : 1 ≤ P.natDegree) : P.derivative ≠ 0 := by
  intro h0
  have h1 := congr_arg (fun q : Polynomial R => q.coeff (P.natDegree - 1)) h0
  rw [Polynomial.coeff_zero, Polynomial.coeff_derivative, Nat.sub_add_cancel hdeg] at h1
  have hcast : ((P.natDegree - 1 : ℕ) : R) + 1 = (P.natDegree : R) := by
    exact_mod_cast Nat.sub_add_cancel hdeg
  rw [hcast] at h1
  have hPne : P ≠ 0 := by rintro rfl; simp at hdeg
  have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hnat : ((P.natDegree : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero hlc hnat h1

noncomputable def cellLeftSign {R : Type*} [Field R] [LinearOrder R]
    (P : Polynomial R) (rs : List R) (j : ℕ) : RSign :=
  if h : 0 < j ∧ j - 1 < rs.length then rsign (P.eval (rs[j - 1]'h.2)) else signAtNegInf P

noncomputable def cellRightSign {R : Type*} [Field R] [LinearOrder R]
    (P : Polynomial R) (rs : List R) (j : ℕ) : RSign :=
  if h : j < rs.length then rsign (P.eval (rs[j]'h)) else signAtPosInf P

lemma exists_left_pt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {P : Polynomial R} (hP : P ≠ 0) {rs : List R} (j : ℕ) (hj : j ≤ rs.length)
    {u : R} (hu : inCell rs j u) :
    ∃ a : R, a < u ∧ rsign (P.eval a) = cellLeftSign P rs j ∧
      ∀ c : R, a < c → c < u → inCell rs j c := by
  by_cases hj0 : 0 < j
  · have hjm : j - 1 < rs.length := by omega
    refine ⟨rs[j - 1]'hjm, hu.1 hj0 hjm, ?_, ?_⟩
    · simp [cellLeftSign, hj0, hjm]
    · intro c hc1 hc2
      exact ⟨fun _ _ => hc1, fun h3 => lt_trans hc2 (hu.2 h3)⟩
  · have hjeq : j = 0 := by omega
    subst hjeq
    obtain ⟨M, _, _, hneg⟩ := exists_sign_at_inf P hP
    let a : R := min (u - 1) (-M - 1)
    refine ⟨a, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_, ?_⟩
    · simp only [cellLeftSign, lt_irrefl, false_and, ↓reduceDIte]
      exact hneg a (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    · intro c _ hc2
      exact ⟨fun h => absurd h (lt_irrefl 0), fun h3 => lt_trans hc2 (hu.2 h3)⟩

lemma exists_right_pt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {P : Polynomial R} (hP : P ≠ 0) {rs : List R} (j : ℕ)
    {u : R} (hu : inCell rs j u) :
    ∃ b : R, u < b ∧ rsign (P.eval b) = cellRightSign P rs j ∧
      ∀ c : R, u < c → c < b → inCell rs j c := by
  by_cases hjlt : j < rs.length
  · refine ⟨rs[j]'hjlt, hu.2 hjlt, ?_, ?_⟩
    · simp [cellRightSign, hjlt]
    · intro c hc1 hc2
      exact ⟨fun h1 h2 => lt_trans (hu.1 h1 h2) hc1, fun _ => hc2⟩
  · obtain ⟨M, _, hpos, _⟩ := exists_sign_at_inf P hP
    let b : R := max (u + 1) (M + 1)
    refine ⟨b, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_, ?_⟩
    · simp only [cellRightSign, hjlt, ↓reduceDIte]
      exact hpos b (lt_of_lt_of_le (by linarith) (le_max_right _ _))
    · intro c hc1 _
      exact ⟨fun h1 h2 => lt_trans (hu.1 h1 h2) hc1, fun h3 => absurd h3 hjlt⟩

lemma cell_root_dichotomy {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasPolyIVT R] {S : Finset (Polynomial R)} {P : Polynomial R}
    (hdeg : 1 ≤ P.natDegree) (hder_mem : P.derivative ∈ S)
    {j : ℕ} (hj : j ≤ (rootList S).length)
    {ε : RSign} (hε : ∀ x : R, inCell (rootList S) j x → rsign (P.derivative.eval x) = ε) :
    -- (1) At most one root in cell j
    (∀ ξ1 ξ2, inCell (rootList S) j ξ1 → inCell (rootList S) j ξ2 → P.eval ξ1 = 0 → P.eval ξ2 = 0 → ξ1 = ξ2) ∧
    -- (2) Root exists iff sL and sR are opposite nonzero signs
    ((∃ ξ, inCell (rootList S) j ξ ∧ P.eval ξ = 0) ↔
      (cellLeftSign P (rootList S) j ≠ .zero ∧ cellRightSign P (rootList S) j ≠ .zero ∧
        cellLeftSign P (rootList S) j ≠ cellRightSign P (rootList S) j)) ∧
    -- (3) Signs around a root
    (∀ ξ, inCell (rootList S) j ξ → P.eval ξ = 0 →
      (∀ x, inCell (rootList S) j x → x < ξ → rsign (P.eval x) = cellLeftSign P (rootList S) j) ∧
      (∀ x, inCell (rootList S) j x → ξ < x → rsign (P.eval x) = cellRightSign P (rootList S) j)) ∧
    -- (4) Sign when no root in cell j
    ((∀ ξ, inCell (rootList S) j ξ → P.eval ξ ≠ 0) →
      ∀ x, inCell (rootList S) j x →
        rsign (P.eval x) = if cellLeftSign P (rootList S) j ≠ .zero then cellLeftSign P (rootList S) j else ε) := by
  set rs := rootList S
  set sL := cellLeftSign P rs j
  set sR := cellRightSign P rs j
  have hPne : P ≠ 0 := by rintro rfl; simp at hdeg
  have hder_ne : P.derivative ≠ 0 := derivative_ne_zero_of_natDegree_pos hdeg
  have hε_ne : ε ≠ .zero := by
    obtain ⟨u, hu⟩ := exists_inCell (rootList_pairwise S) hj
    intro h0
    rw [← hε u hu, rsign_zero_iff] at h0
    exact no_root_inCell hder_mem hder_ne hj hu h0
  have hneg_neg : ∀ s : RSign, s.negate.negate = s := fun s => by cases s <;> rfl
  have hsub_interval : ∀ {x y c : R}, inCell rs j x → inCell rs j y → x < c → c < y → inCell rs j c :=
    fun hx hy hc1 hc2 =>
      ⟨fun h1 h2 => lt_trans (hx.1 h1 h2) hc1, fun h3 => lt_trans hc2 (hy.2 h3)⟩
  -- Part 1: uniqueness
  have huniq : ∀ ξ1 ξ2, inCell rs j ξ1 → inCell rs j ξ2 → P.eval ξ1 = 0 → P.eval ξ2 = 0 → ξ1 = ξ2 := by
    intro ξ1 ξ2 h1 h2 e1 e2
    rcases lt_trichotomy ξ1 ξ2 with hlt | heq | hgt
    · obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.rolle P hlt (e1.trans e2.symm)
      exact absurd hce (no_root_inCell hder_mem hder_ne hj (hsub_interval h1 h2 hc1 hc2))
    · exact heq
    · obtain ⟨c, hc1, hc2, hce⟩ := HasPolyIVT.rolle P hgt (e2.trans e1.symm)
      exact absurd hce (no_root_inCell hder_mem hder_ne hj (hsub_interval h2 h1 hc1 hc2))
  -- Helper: if ξ ∈ cell j is a root, sL = ε.negate and sR = ε
  have hroot_signs : ∀ ξ, inCell rs j ξ → P.eval ξ = 0 →
      sL = ε.negate ∧ sR = ε ∧
      (∀ x, inCell rs j x → x < ξ → rsign (P.eval x) = ε.negate) ∧
      (∀ x, inCell rs j x → ξ < x → rsign (P.eval x) = ε) := by
    intro ξ hξ hPξ
    have hsL : sL = ε.negate := by
      obtain ⟨a, ha, hasign, haint⟩ := exists_left_pt hPne j hj hξ
      obtain ⟨c, hc1, hc2, hmvt⟩ := HasPolyIVT.mvt P ha
      rw [hPξ, zero_sub] at hmvt
      have hneg_sign : rsign (-P.eval a) = ε := by
        rw [hmvt, mul_comm, rsign_mul_pos (sub_pos.mpr ha)]
        exact hε c (haint c hc1 hc2)
      rw [rsign_neg] at hneg_sign
      calc sL = rsign (P.eval a) := hasign.symm
        _ = (rsign (P.eval a)).negate.negate := (hneg_neg _).symm
        _ = ε.negate := congr_arg RSign.negate hneg_sign
    have hsR : sR = ε := by
      obtain ⟨b, hb, hbsign, hbint⟩ := exists_right_pt hPne j hξ
      obtain ⟨c, hc1, hc2, hmvt⟩ := HasPolyIVT.mvt P hb
      rw [hPξ, sub_zero] at hmvt
      have hrb : rsign (P.eval b) = ε := by
        rw [hmvt, mul_comm, rsign_mul_pos (sub_pos.mpr hb)]
        exact hε c (hbint c hc1 hc2)
      exact hbsign.symm.trans hrb
    refine ⟨hsL, hsR, ?_, ?_⟩
    · intro x hx hlt
      obtain ⟨c, hc1, hc2, hmvt⟩ := HasPolyIVT.mvt P hlt
      rw [hPξ, zero_sub] at hmvt
      have hneg_sign : rsign (-P.eval x) = ε := by
        rw [hmvt, mul_comm, rsign_mul_pos (sub_pos.mpr hlt)]
        exact hε c (hsub_interval hx hξ hc1 hc2)
      rw [rsign_neg] at hneg_sign
      calc rsign (P.eval x) = (rsign (P.eval x)).negate.negate := (hneg_neg _).symm
        _ = ε.negate := congr_arg RSign.negate hneg_sign
    · intro x hx hlt
      obtain ⟨c, hc1, hc2, hmvt⟩ := HasPolyIVT.mvt P hlt
      rw [hPξ, sub_zero] at hmvt
      rw [hmvt, mul_comm, rsign_mul_pos (sub_pos.mpr hlt)]
      exact hε c (hsub_interval hξ hx hc1 hc2)
  refine ⟨huniq, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨ξ, hξ, hPξ⟩
      obtain ⟨hsL, hsR, _, _⟩ := hroot_signs ξ hξ hPξ
      rw [hsL, hsR]
      cases h : ε <;> simp_all [RSign.negate]
    · rintro ⟨hsL0, hsR0, hne⟩
      obtain ⟨u, hu⟩ := exists_inCell (rootList_pairwise S) hj
      obtain ⟨a, ha, hasign, haint⟩ := exists_left_pt hPne j hj hu
      obtain ⟨b, hb, hbsign, hbint⟩ := exists_right_pt hPne j hu
      have hprod : P.eval a * P.eval b < 0 := by
        have ha_s : rsign (P.eval a) = sL := hasign
        have hb_s : rsign (P.eval b) = sR := hbsign
        cases h1 : sL <;> cases h2 : sR
        all_goals try exact absurd h1 hsL0
        all_goals try exact absurd h2 hsR0
        all_goals try exact absurd (h1.trans h2.symm) hne
        · exact mul_neg_of_neg_of_pos (rsign_neg_iff.mp (ha_s.trans h1)) (rsign_pos_iff.mp (hb_s.trans h2))
        · exact mul_neg_of_pos_of_neg (rsign_pos_iff.mp (ha_s.trans h1)) (rsign_neg_iff.mp (hb_s.trans h2))
      obtain ⟨ξ, hξ1, hξ2, hPξ⟩ := HasPolyIVT.ivt_both (lt_trans ha hb) hprod
      refine ⟨ξ, ?_, hPξ⟩
      rcases lt_trichotomy ξ u with hlt | rfl | hgt
      · exact haint ξ hξ1 hlt
      · exact hu
      · exact hbint ξ hgt hξ2
  · intro ξ hξ hPξ
    obtain ⟨hsL, hsR, hL, hR⟩ := hroot_signs ξ hξ hPξ
    exact ⟨fun x hx hlt => (hL x hx hlt).trans hsL.symm,
      fun x hx hlt => (hR x hx hlt).trans hsR.symm⟩
  · intro hno x hx
    obtain ⟨a, ha, hasign, haint⟩ := exists_left_pt hPne j hj hx
    split_ifs with hsL0
    · by_contra hne
      have hprod : P.eval a * P.eval x < 0 := by
        have hx0 : rsign (P.eval x) ≠ .zero := mt rsign_zero_iff.mp (hno x hx)
        cases h1 : sL <;> cases h2 : rsign (P.eval x)
        all_goals try exact absurd h1 hsL0
        all_goals try exact absurd h2 hx0
        all_goals try exact absurd (h2.trans h1.symm) hne
        · exact mul_neg_of_neg_of_pos (rsign_neg_iff.mp (hasign.trans h1)) (rsign_pos_iff.mp h2)
        · exact mul_neg_of_pos_of_neg (rsign_pos_iff.mp (hasign.trans h1)) (rsign_neg_iff.mp h2)
      obtain ⟨ξ, hξ1, hξ2, hPξ⟩ := HasPolyIVT.ivt_both ha hprod
      exact hno ξ (haint ξ hξ1 hξ2) hPξ
    · have hsLzero : sL = .zero := not_not.mp hsL0
      have hPa : P.eval a = 0 := rsign_zero_iff.mp (hasign.trans hsLzero)
      obtain ⟨c, hc1, hc2, hmvt⟩ := HasPolyIVT.mvt P ha
      rw [hPa, sub_zero] at hmvt
      rw [hmvt, mul_comm, rsign_mul_pos (sub_pos.mpr ha)]
      exact hε c (haint c hc1 hc2)

/-! #### Tag list construction for inserting one polynomial into a `SameSignTable` -/

def tagPos {r : ℕ} : Fin r ⊕ Fin (r + 1) → ℕ
  | Sum.inr j => 2 * j.val
  | Sum.inl i => 2 * i.val + 1

def buildTags (r : ℕ) (hasRoot : Fin (r + 1) → Bool) : List (Fin r ⊕ Fin (r + 1)) :=
  (List.finRange (r + 1)).flatMap fun j =>
    (if hasRoot j then [Sum.inr j] else []) ++
    (if h : j.val < r then [Sum.inl ⟨j.val, h⟩] else [])

lemma mem_buildTags_inl {r : ℕ} (hasRoot : Fin (r + 1) → Bool) (i : Fin r) :
    Sum.inl i ∈ buildTags r hasRoot := by
  unfold buildTags
  rw [List.mem_flatMap]
  refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, List.mem_finRange _, ?_⟩
  simp [i.isLt]

lemma mem_buildTags_inr {r : ℕ} (hasRoot : Fin (r + 1) → Bool) (j : Fin (r + 1)) :
    Sum.inr j ∈ buildTags r hasRoot ↔ hasRoot j = true := by
  unfold buildTags
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨j', _, hj'⟩
    simp only [List.mem_append] at hj'
    rcases hj' with h1 | h2
    · split_ifs at h1 with hr
      · simp only [List.mem_singleton, Sum.inr.injEq] at h1; subst h1; exact hr
      · simp at h1
    · split_ifs at h2 with hlt <;> simp at h2
  · intro hr
    refine ⟨j, List.mem_finRange _, ?_⟩
    simp [hr]

lemma buildTags_pairwise {r : ℕ} (hasRoot : Fin (r + 1) → Bool) :
    (buildTags r hasRoot).Pairwise (fun a b => tagPos a < tagPos b) := by
  unfold buildTags
  have hfr : (List.finRange (r + 1)).Pairwise (· < ·) := List.pairwise_lt_finRange (r + 1)
  have hstep : ∀ (ls : List (Fin (r + 1))), ls.Pairwise (· < ·) →
      (ls.flatMap fun j =>
        (if hasRoot j then [Sum.inr j] else []) ++
        (if h : j.val < r then [Sum.inl ⟨j.val, h⟩] else [])).Pairwise
        (fun a b => tagPos a < tagPos b) := by
    intro ls hpw
    induction ls with
    | nil => simp
    | cons j ls ih =>
      simp only [List.flatMap_cons]
      rw [List.pairwise_append]
      have hblock_mem : ∀ x ∈ (if hasRoot j then [Sum.inr j] else []) ++
          (if h : j.val < r then [Sum.inl ⟨j.val, h⟩] else []),
          tagPos x ≤ 2 * j.val + 1 := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with h1 | h2
        · split_ifs at h1 with hr
          · simp only [List.mem_singleton] at h1; subst h1; simp [tagPos]
          · simp at h1
        · split_ifs at h2 with hlt
          · simp only [List.mem_singleton] at h2; subst h2; simp [tagPos]
          · simp at h2
      refine ⟨?_, ih (List.pairwise_cons.mp hpw).2, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨?_, ?_, ?_⟩
        · split_ifs <;> simp
        · split_ifs <;> simp
        · intro a ha b hb
          split_ifs at ha with hr
          · simp only [List.mem_singleton] at ha; subst ha
            split_ifs at hb with hlt
            · simp only [List.mem_singleton] at hb; subst hb; simp [tagPos]
            · simp at hb
          · simp at ha
      · intro a ha b hb
        have ha_le := hblock_mem a ha
        rw [List.mem_flatMap] at hb
        obtain ⟨j', hj', hb'⟩ := hb
        have hjj' : j < j' := (List.pairwise_cons.mp hpw).1 j' hj'
        have hb_ge : 2 * j'.val ≤ tagPos b := by
          simp only [List.mem_append] at hb'
          rcases hb' with h1 | h2
          · split_ifs at h1 with hr
            · simp only [List.mem_singleton] at h1; subst h1; simp [tagPos]
            · simp at h1
          · split_ifs at h2 with hlt
            · simp only [List.mem_singleton] at h2; subst h2; simp [tagPos]
            · simp at h2
        have : j.val < j'.val := hjj'
        omega
  exact hstep _ hfr

lemma buildTags_enclosingCell {r : ℕ} (hasRoot : Fin (r + 1) → Bool) (m : ℕ) :
    ∃ j : ℕ, j ≤ r ∧
      ∀ (i : Fin r) (idx : ℕ) (hidx : idx < (buildTags r hasRoot).length),
        (buildTags r hasRoot)[idx]'hidx = Sum.inl i → (idx < m ↔ i.val < j) := by
  classical
  set tags := buildTags r hasRoot
  let leftsBefore : List (Fin r ⊕ Fin (r + 1)) := (tags.take m).filter (fun t => t.isLeft)
  let j : ℕ := leftsBefore.length
  have htags_pw : tags.Pairwise (fun a b => tagPos a < tagPos b) := buildTags_pairwise hasRoot
  have hnd_tags : tags.Nodup :=
    htags_pw.imp fun {a b} (h : tagPos a < tagPos b) heq => by rw [heq] at h; exact lt_irrefl _ h
  have hnd : leftsBefore.Nodup :=
    hnd_tags.sublist (List.filter_sublist.trans (List.take_sublist _ _))
  have hinl_idx : ∀ i : Fin r, ∃ (idx : ℕ) (hidx : idx < tags.length), tags[idx]'hidx = Sum.inl i :=
    fun i => List.mem_iff_getElem.mp (mem_buildTags_inl hasRoot i)
  have hidx_mono : ∀ (i1 i2 : Fin r) (idx1 idx2 : ℕ) (h1 : idx1 < tags.length) (h2 : idx2 < tags.length),
      tags[idx1]'h1 = Sum.inl i1 → tags[idx2]'h2 = Sum.inl i2 → (idx1 < idx2 ↔ i1.val < i2.val) := by
    intro i1 i2 idx1 idx2 h1 h2 e1 e2
    constructor
    · intro hlt
      have := List.pairwise_iff_getElem.mp htags_pw idx1 idx2 h1 h2 hlt
      rw [e1, e2] at this; simp [tagPos] at this; omega
    · intro hlt
      rcases lt_trichotomy idx1 idx2 with h | rfl | h
      · exact h
      · rw [e1] at e2; cases e2; omega
      · have := List.pairwise_iff_getElem.mp htags_pw idx2 idx1 h2 h1 h
        rw [e1, e2] at this; simp [tagPos] at this; omega
  have hj_le_r : j ≤ r := by
    have hsub : leftsBefore.toFinset ⊆ Finset.univ.image (Sum.inl : Fin r → Fin r ⊕ Fin (r + 1)) := by
      intro t ht
      rw [List.mem_toFinset] at ht
      have hL := (List.mem_filter.mp ht).2
      cases t with
      | inl i => exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      | inr _ => simp at hL
    calc j = leftsBefore.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (Finset.univ.image (Sum.inl : Fin r → Fin r ⊕ Fin (r + 1))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := by simp
  refine ⟨j, hj_le_r, ?_⟩
  intro i idx hidx htag
  let S_lt : Finset (Fin r) := Finset.univ.filter (fun i' => Sum.inl i' ∈ tags.take m)
  have hS_card : S_lt.card = j := by
    rw [show j = leftsBefore.toFinset.card from (List.toFinset_card_of_nodup hnd).symm]
    have heq_set : leftsBefore.toFinset = S_lt.image Sum.inl := by
      ext t
      simp only [leftsBefore, List.mem_toFinset, List.mem_filter, Finset.mem_image, S_lt,
        Finset.mem_filter, Finset.mem_univ, true_and]
      cases t with
      | inl i' => simp
      | inr j' => simp
    rw [heq_set, Finset.card_image_of_injective _ Sum.inl_injective]
  have hS_down : ∀ a b : Fin r, a.val < b.val → b ∈ S_lt → a ∈ S_lt := by
    intro a b hab hb
    simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨ib, hib, htb⟩ := List.mem_iff_getElem.mp hb
    obtain ⟨ia, hia, hta⟩ := hinl_idx a
    have hib_lt : ib < m := by simp at hib; omega
    have hib_t : ib < tags.length := by simp at hib; omega
    have htb' : tags[ib]'hib_t = Sum.inl b := by simpa using htb
    have hia_lt : ia < ib := (hidx_mono a b ia ib hia hib_t hta htb').mpr hab
    exact List.mem_iff_getElem.mpr ⟨ia, by simp; omega, by simpa using hta⟩
  have hS_iff : ∀ a : Fin r, a ∈ S_lt ↔ a.val < j := by
    intro a
    have hset_eq : S_lt = Finset.univ.filter (fun a : Fin r => a.val < j) := by
      by_contra hneq
      have hcard_eq : S_lt.card = (Finset.univ.filter (fun a : Fin r => a.val < j)).card := by
        rw [hS_card]
        have : (Finset.univ.filter (fun a : Fin r => a.val < j)).card = j := by
          have hbij : Finset.univ.filter (fun a : Fin r => a.val < j) =
              (Finset.univ : Finset (Fin j)).image (fun x => ⟨x.val, lt_of_lt_of_le x.isLt hj_le_r⟩) := by
            ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hx; exact ⟨⟨x.val, hx⟩, rfl⟩
            · rintro ⟨y, rfl⟩; exact y.isLt
          rw [hbij, Finset.card_image_of_injective]
          · simp
          · intro x y hxy; simp only [Fin.mk.injEq] at hxy; exact Fin.ext hxy
        exact this.symm
      have hex_ge : ∃ b ∈ S_lt, j ≤ b.val := by
        by_contra hall; push Not at hall
        have hsub : S_lt ⊆ Finset.univ.filter (fun a : Fin r => a.val < j) :=
          fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall x hx⟩
        exact hneq (Finset.eq_of_subset_of_card_le hsub hcard_eq.ge)
      obtain ⟨b, hbS, hbj⟩ := hex_ge
      have hsub : Finset.univ.filter (fun a : Fin r => a.val < j) ⊆ S_lt := by
        intro x hx
        have hxj : x.val < j := (Finset.mem_filter.mp hx).2
        exact hS_down x b (lt_of_lt_of_le hxj hbj) hbS
      exact hneq (Finset.eq_of_subset_of_card_le hsub hcard_eq.le).symm
    rw [hset_eq]; simp
  rw [← hS_iff i]
  simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hlt
    exact List.mem_iff_getElem.mpr ⟨idx, by simp; omega, by simpa using htag⟩
  · intro hmem
    obtain ⟨idx', hidx', htag'⟩ := List.mem_iff_getElem.mp hmem
    have hidx'_lt : idx' < m := by simp at hidx'; omega
    have hidx'_t : idx' < tags.length := by simp at hidx'; omega
    have htag'' : tags[idx']'hidx'_t = Sum.inl i := by simpa using htag'
    have heq_idx : idx = idx' := by
      rcases lt_trichotomy idx idx' with h | h | h
      · exact absurd ((hidx_mono i i idx idx' hidx hidx'_t htag htag'').mp h) (lt_irrefl _)
      · exact h
      · exact absurd ((hidx_mono i i idx' idx hidx'_t hidx htag'' htag).mp h) (lt_irrefl _)
    omega

lemma SameSignTable.insert_poly {A R₁ R₂ : Type*} [CommRing A] [DecidableEq (Polynomial A)]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁] [HasPolyIVT R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂] [HasPolyIVT R₂]
    {F_base : Finset (Polynomial A)} {p : Polynomial A} {φ₁ : A →+* R₁} {φ₂ : A →+* R₂}
    (hdeg1 : 1 ≤ (p.map φ₁).natDegree) (hdeg2 : 1 ≤ (p.map φ₂).natDegree)
    (hdeg_eq : (p.map φ₁).natDegree = (p.map φ₂).natDegree)
    (hlc : rsign (p.map φ₁).leadingCoeff = rsign (p.map φ₂).leadingCoeff)
    (hST : SameSignTable (insert p.derivative F_base) φ₁ φ₂)
    (hat_roots : ∀ (i : ℕ)
      (h1 : i < (rootList ((insert p.derivative F_base).image (Polynomial.map φ₁))).length)
      (h2 : i < (rootList ((insert p.derivative F_base).image (Polynomial.map φ₂))).length),
      rsign ((p.map φ₁).eval ((rootList ((insert p.derivative F_base).image (Polynomial.map φ₁)))[i]'h1)) =
      rsign ((p.map φ₂).eval ((rootList ((insert p.derivative F_base).image (Polynomial.map φ₂)))[i]'h2))) :
    SameSignTable (insert p (insert p.derivative F_base)) φ₁ φ₂ := by
  let S := insert p.derivative F_base
  let S1 := S.image (Polynomial.map φ₁)
  let S2 := S.image (Polynomial.map φ₂)
  let P1 := p.map φ₁
  let P2 := p.map φ₂
  let rs1 := rootList S1
  let rs2 := rootList S2
  let r := rs1.length
  have hr2 : rs2.length = r := hST.len_eq.symm
  have hder1_mem : P1.derivative ∈ S1 := by
    dsimp only [P1]
    rw [Polynomial.derivative_map]
    exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
  have hder2_mem : P2.derivative ∈ S2 := by
    dsimp only [P2]
    rw [Polynomial.derivative_map]
    exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
  -- Common derivative sign ε j, left sign sL j, right sign sR j on each cell j : Fin (r + 1)
  have hsL_eq : ∀ j : Fin (r + 1), cellLeftSign P1 rs1 j.val = cellLeftSign P2 rs2 j.val := by
    intro j
    unfold cellLeftSign
    by_cases hj0 : 0 < j.val
    · have h1 : 0 < j.val ∧ j.val - 1 < rs1.length := ⟨hj0, by omega⟩
      have h2 : 0 < j.val ∧ j.val - 1 < rs2.length := ⟨hj0, by omega⟩
      rw [dif_pos h1, dif_pos h2]
      exact hat_roots (j.val - 1) h1.2 h2.2
    · have h1 : ¬ (0 < j.val ∧ j.val - 1 < rs1.length) := fun h => hj0 h.1
      have h2 : ¬ (0 < j.val ∧ j.val - 1 < rs2.length) := fun h => hj0 h.1
      rw [dif_neg h1, dif_neg h2]
      simp only [signAtNegInf, P1, P2, hdeg_eq, hlc]
  have hsR_eq : ∀ j : Fin (r + 1), cellRightSign P1 rs1 j.val = cellRightSign P2 rs2 j.val := by
    intro j
    unfold cellRightSign
    by_cases hjlt : j.val < r
    · have h1 : j.val < rs1.length := hjlt
      have h2 : j.val < rs2.length := hr2.symm ▸ hjlt
      rw [dif_pos h1, dif_pos h2]
      exact hat_roots j.val h1 h2
    · have h1 : ¬ j.val < rs1.length := hjlt
      have h2 : ¬ j.val < rs2.length := by omega
      rw [dif_neg h1, dif_neg h2]
      exact hlc
  let ε : Fin (r + 1) → RSign := fun j =>
    let x1 := Classical.choose (exists_inCell (rootList_pairwise S1) (Nat.le_of_lt_succ j.isLt))
    rsign (P1.derivative.eval x1)
  have hε1 : ∀ (j : Fin (r + 1)) (x : R₁), inCell rs1 j.val x → rsign (P1.derivative.eval x) = ε j := by
    intro j x hx
    exact const_sign_inCell hder1_mem (Nat.le_of_lt_succ j.isLt) hx
      (Classical.choose_spec (exists_inCell (rootList_pairwise S1) (Nat.le_of_lt_succ j.isLt)))
  have hε2 : ∀ (j : Fin (r + 1)) (x : R₂), inCell rs2 j.val x → rsign (P2.derivative.eval x) = ε j := by
    intro j x hx
    let x1 := Classical.choose (exists_inCell (rootList_pairwise S1) (Nat.le_of_lt_succ j.isLt))
    have hx1 : inCell rs1 j.val x1 :=
      Classical.choose_spec (exists_inCell (rootList_pairwise S1) (Nat.le_of_lt_succ j.isLt))
    have hst := hST.at_cells j.val (Nat.le_of_lt_succ j.isLt) x1 x hx1 hx p.derivative
      (Finset.mem_insert_self _ _)
    rw [← Polynomial.derivative_map, ← Polynomial.derivative_map] at hst
    exact hst.symm
  let hasRoot : Fin (r + 1) → Bool := fun j =>
    decide (cellLeftSign P1 rs1 j.val ≠ .zero ∧ cellRightSign P1 rs1 j.val ≠ .zero ∧
      cellLeftSign P1 rs1 j.val ≠ cellRightSign P1 rs1 j.val)
  have hdic1 := fun j : Fin (r + 1) =>
    cell_root_dichotomy hdeg1 hder1_mem (Nat.le_of_lt_succ j.isLt) (hε1 j)
  have hdic2 := fun j : Fin (r + 1) =>
    cell_root_dichotomy hdeg2 hder2_mem (by change j.val ≤ rs2.length; omega) (hε2 j)
  have hex1 : ∀ j : Fin (r + 1), hasRoot j = true ↔ ∃ ξ : R₁, inCell rs1 j.val ξ ∧ P1.eval ξ = 0 := by
    intro j; simp only [hasRoot, decide_eq_true_eq]; exact (hdic1 j).2.1.symm
  have hex2 : ∀ j : Fin (r + 1), hasRoot j = true ↔ ∃ ξ : R₂, inCell rs2 j.val ξ ∧ P2.eval ξ = 0 := by
    intro j; simp only [hasRoot, decide_eq_true_eq, hsL_eq j, hsR_eq j]; exact (hdic2 j).2.1.symm
  let ξ1 : Fin (r + 1) → R₁ := fun j =>
    if h : hasRoot j = true then Classical.choose ((hex1 j).mp h) else 0
  let ξ2 : Fin (r + 1) → R₂ := fun j =>
    if h : hasRoot j = true then Classical.choose ((hex2 j).mp h) else 0
  have hξ1_spec : ∀ j, hasRoot j = true → inCell rs1 j.val (ξ1 j) ∧ P1.eval (ξ1 j) = 0 := by
    intro j hj; simp only [ξ1, dif_pos hj]; exact Classical.choose_spec ((hex1 j).mp hj)
  have hξ2_spec : ∀ j, hasRoot j = true → inCell rs2 j.val (ξ2 j) ∧ P2.eval (ξ2 j) = 0 := by
    intro j hj; simp only [ξ2, dif_pos hj]; exact Classical.choose_spec ((hex2 j).mp hj)
  let tags := buildTags r hasRoot
  let eval1 : Fin r ⊕ Fin (r + 1) → R₁
    | Sum.inl i => rs1[i.val]'i.isLt
    | Sum.inr j => ξ1 j
  let eval2 : Fin r ⊕ Fin (r + 1) → R₂
    | Sum.inl i => rs2[i.val]'(hr2.symm ▸ i.isLt)
    | Sum.inr j => ξ2 j
  let μ1 : List R₁ := tags.map eval1
  let μ2 : List R₂ := tags.map eval2
  -- Monotonicity of eval1 and eval2 on tags
  have heval1_lt : ∀ a ∈ tags, ∀ b ∈ tags, tagPos a < tagPos b → eval1 a < eval1 b := by
    intro a ha b hb hlt
    cases a with
    | inl i1 => cases b with
      | inl i2 =>
        exact pairwise_lt_get (rootList_pairwise S1) i1.isLt i2.isLt (by simp [tagPos] at hlt; omega)
      | inr j2 =>
        have hspec := (hξ1_spec j2 ((mem_buildTags_inr hasRoot j2).mp hb)).1
        have hlt_cell := hspec.1 (by simp [tagPos] at hlt; omega) (by simp [tagPos] at hlt; omega)
        have hle : rs1[i1.val]'i1.isLt ≤ rs1[j2.val - 1]'(by simp [tagPos] at hlt; omega) := by
          rcases eq_or_lt_of_le (show i1.val ≤ j2.val - 1 by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S1) _ _ hlt')
        exact lt_of_le_of_lt hle hlt_cell
    | inr j1 => cases b with
      | inl i2 =>
        have hspec := (hξ1_spec j1 ((mem_buildTags_inr hasRoot j1).mp ha)).1
        have hlt_cell := hspec.2 (by simp [tagPos] at hlt; omega)
        have hle : rs1[j1.val]'(by simp [tagPos] at hlt; omega) ≤ rs1[i2.val]'i2.isLt := by
          rcases eq_or_lt_of_le (show j1.val ≤ i2.val by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S1) _ _ hlt')
        exact lt_of_lt_of_le hlt_cell hle
      | inr j2 =>
        have hspec1 := (hξ1_spec j1 ((mem_buildTags_inr hasRoot j1).mp ha)).1
        have hspec2 := (hξ1_spec j2 ((mem_buildTags_inr hasRoot j2).mp hb)).1
        have hj1lt : j1.val < r := by simp [tagPos] at hlt; omega
        have h1 := hspec1.2 hj1lt
        have h2 := hspec2.1 (by simp [tagPos] at hlt; omega) (by simp [tagPos] at hlt; omega)
        have hle : rs1[j1.val]'hj1lt ≤ rs1[j2.val - 1]'(by simp [tagPos] at hlt; omega) := by
          rcases eq_or_lt_of_le (show j1.val ≤ j2.val - 1 by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S1) _ _ hlt')
        exact lt_trans (lt_of_lt_of_le h1 hle) h2
  have heval2_lt : ∀ a ∈ tags, ∀ b ∈ tags, tagPos a < tagPos b → eval2 a < eval2 b := by
    intro a ha b hb hlt
    cases a with
    | inl i1 => cases b with
      | inl i2 =>
        exact pairwise_lt_get (rootList_pairwise S2) (hr2.symm ▸ i1.isLt) (hr2.symm ▸ i2.isLt)
          (by simp [tagPos] at hlt; omega)
      | inr j2 =>
        have hspec := (hξ2_spec j2 ((mem_buildTags_inr hasRoot j2).mp hb)).1
        have hlt_cell := hspec.1 (by simp [tagPos] at hlt; omega) (by simp [tagPos] at hlt; omega)
        have hle : rs2[i1.val]'(hr2.symm ▸ i1.isLt) ≤ rs2[j2.val - 1]'(by simp [tagPos] at hlt; omega) := by
          rcases eq_or_lt_of_le (show i1.val ≤ j2.val - 1 by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S2) _ _ hlt')
        exact lt_of_le_of_lt hle hlt_cell
    | inr j1 => cases b with
      | inl i2 =>
        have hspec := (hξ2_spec j1 ((mem_buildTags_inr hasRoot j1).mp ha)).1
        have hlt_cell := hspec.2 (by simp [tagPos] at hlt; omega)
        have hle : rs2[j1.val]'(by simp [tagPos] at hlt; omega) ≤ rs2[i2.val]'(hr2.symm ▸ i2.isLt) := by
          rcases eq_or_lt_of_le (show j1.val ≤ i2.val by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S2) _ _ hlt')
        exact lt_of_lt_of_le hlt_cell hle
      | inr j2 =>
        have hspec1 := (hξ2_spec j1 ((mem_buildTags_inr hasRoot j1).mp ha)).1
        have hspec2 := (hξ2_spec j2 ((mem_buildTags_inr hasRoot j2).mp hb)).1
        have hj1lt : j1.val < rs2.length := by simp [tagPos] at hlt; omega
        have h1 := hspec1.2 hj1lt
        have h2 := hspec2.1 (by simp [tagPos] at hlt; omega) (by simp [tagPos] at hlt; omega)
        have hle : rs2[j1.val]'hj1lt ≤ rs2[j2.val - 1]'(by simp [tagPos] at hlt; omega) := by
          rcases eq_or_lt_of_le (show j1.val ≤ j2.val - 1 by simp [tagPos] at hlt; omega) with heq | hlt'
          · simp [heq]
          · exact le_of_lt (pairwise_lt_get (rootList_pairwise S2) _ _ hlt')
        exact lt_trans (lt_of_lt_of_le h1 hle) h2
  have hμ1_pw : μ1.Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij =>
      heval1_lt _ (List.getElem_mem hi) _ (List.getElem_mem hj)
        (List.pairwise_iff_getElem.mp (buildTags_pairwise hasRoot) i j hi hj hij))
  have hμ2_pw : μ2.Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij =>
      heval2_lt _ (List.getElem_mem hi) _ (List.getElem_mem hj)
        (List.pairwise_iff_getElem.mp (buildTags_pairwise hasRoot) i j hi hj hij))
  have hP1ne : P1 ≠ 0 := by rintro h0; change 1 ≤ P1.natDegree at hdeg1; rw [h0] at hdeg1; simp at hdeg1
  have hP2ne : P2 ≠ 0 := by rintro h0; change 1 ≤ P2.natDegree at hdeg2; rw [h0] at hdeg2; simp at hdeg2
  -- Show rootList ((insert p S).image (map φ₁)) = μ1 and similarly for μ2
  have hμ1_eq : rootList ((insert p S).image (Polynomial.map φ₁)) = μ1 := by
    apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _) hμ1_pw
    intro x
    rw [mem_rootList, Finset.image_insert]
    constructor
    · rintro ⟨q, hq, hq0, hqx⟩
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · rcases point_position (rootList_pairwise S1) x with ⟨i, hi, rfl⟩ | ⟨j, hj, hcell⟩
        · exact List.mem_map.mpr ⟨Sum.inl ⟨i, hi⟩, mem_buildTags_inl hasRoot ⟨i, hi⟩, rfl⟩
        · let jF : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
          have hhr : hasRoot jF = true := (hex1 jF).mpr ⟨x, hcell, hqx⟩
          have heq : x = ξ1 jF := (hdic1 jF).1 x (ξ1 jF) hcell (hξ1_spec jF hhr).1 hqx (hξ1_spec jF hhr).2
          exact List.mem_map.mpr ⟨Sum.inr jF, (mem_buildTags_inr hasRoot jF).mpr hhr, heq.symm⟩
      · have hxrs : x ∈ rs1 := (mem_rootList S1 x).mpr ⟨q, hqS, hq0, hqx⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxrs
        exact List.mem_map.mpr ⟨Sum.inl ⟨i, hi⟩, mem_buildTags_inl hasRoot ⟨i, hi⟩, rfl⟩
    · intro hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      cases t with
      | inl i =>
        obtain ⟨q, hqS, hq0, hqx⟩ := (mem_rootList S1 _).mp (List.getElem_mem i.isLt)
        exact ⟨q, Finset.mem_insert_of_mem hqS, hq0, hqx⟩
      | inr j =>
        exact ⟨P1, Finset.mem_insert_self _ _, hP1ne,
          (hξ1_spec j ((mem_buildTags_inr hasRoot j).mp ht)).2⟩
  have hμ2_eq : rootList ((insert p S).image (Polynomial.map φ₂)) = μ2 := by
    apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _) hμ2_pw
    intro x
    rw [mem_rootList, Finset.image_insert]
    constructor
    · rintro ⟨q, hq, hq0, hqx⟩
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · rcases point_position (rootList_pairwise S2) x with ⟨i, hi, rfl⟩ | ⟨j, hj, hcell⟩
        · exact List.mem_map.mpr ⟨Sum.inl ⟨i, hr2 ▸ hi⟩, mem_buildTags_inl hasRoot ⟨i, hr2 ▸ hi⟩, rfl⟩
        · let jF : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le (hr2 ▸ hj)⟩
          have hhr : hasRoot jF = true := (hex2 jF).mpr ⟨x, hcell, hqx⟩
          have heq : x = ξ2 jF := (hdic2 jF).1 x (ξ2 jF) hcell (hξ2_spec jF hhr).1 hqx (hξ2_spec jF hhr).2
          exact List.mem_map.mpr ⟨Sum.inr jF, (mem_buildTags_inr hasRoot jF).mpr hhr, heq.symm⟩
      · have hxrs : x ∈ rs2 := (mem_rootList S2 x).mpr ⟨q, hqS, hq0, hqx⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxrs
        exact List.mem_map.mpr ⟨Sum.inl ⟨i, hr2 ▸ hi⟩, mem_buildTags_inl hasRoot ⟨i, hr2 ▸ hi⟩, rfl⟩
    · intro hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      cases t with
      | inl i =>
        have hi2 : i.val < rs2.length := hr2.symm ▸ i.isLt
        obtain ⟨q, hqS, hq0, hqx⟩ := (mem_rootList S2 _).mp (List.getElem_mem (l := rs2) hi2)
        exact ⟨q, Finset.mem_insert_of_mem hqS, hq0, hqx⟩
      | inr j =>
        exact ⟨P2, Finset.mem_insert_self _ _, hP2ne,
          (hξ2_spec j ((mem_buildTags_inr hasRoot j).mp ht)).2⟩
  have hlen1 : (rootList ((insert p S).image (Polynomial.map φ₁))).length = tags.length := by
    rw [hμ1_eq]; simp only [μ1, List.length_map]
  have hlen2 : (rootList ((insert p S).image (Polynomial.map φ₂))).length = tags.length := by
    rw [hμ2_eq]; simp only [μ2, List.length_map]
  have hget1 : ∀ (k : ℕ) (hk : k < tags.length),
      (rootList ((insert p S).image (Polynomial.map φ₁)))[k]'(hlen1.symm ▸ hk) = eval1 (tags[k]'hk) := by
    intro k hk; simp only [hμ1_eq, μ1, List.getElem_map]
  have hget2 : ∀ (k : ℕ) (hk : k < tags.length),
      (rootList ((insert p S).image (Polynomial.map φ₂)))[k]'(hlen2.symm ▸ hk) = eval2 (tags[k]'hk) := by
    intro k hk; simp only [hμ2_eq, μ2, List.getElem_map]
  refine ⟨by rw [hlen1, hlen2], ?_, ?_⟩
  · intro m hm1 hm2 q hq
    have hmt : m < tags.length := hlen1 ▸ hm1
    rw [hget1 m hmt, hget2 m hmt]
    cases ht : tags[m]'hmt with
    | inl i =>
      dsimp [eval1, eval2]
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · exact hat_roots i.val i.isLt (hr2.symm ▸ i.isLt)
      · exact hST.at_roots i.val i.isLt (hr2.symm ▸ i.isLt) q hqS
    | inr j =>
      dsimp [eval1, eval2]
      have hhr : hasRoot j = true := (mem_buildTags_inr hasRoot j).mp (ht ▸ List.getElem_mem hmt)
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · change rsign (P1.eval (ξ1 j)) = rsign (P2.eval (ξ2 j))
        rw [(hξ1_spec j hhr).2, (hξ2_spec j hhr).2, rsign_zero_iff.mpr rfl, rsign_zero_iff.mpr rfl]
      · exact hST.at_cells j.val (Nat.le_of_lt_succ j.isLt) (ξ1 j) (ξ2 j)
          (hξ1_spec j hhr).1 (hξ2_spec j hhr).1 q hqS
  · intro m hm x1 x2 hx1 hx2 q hq
    have hmt : m ≤ tags.length := hlen1 ▸ hm
    have htags_pw := buildTags_pairwise hasRoot
    have hinl_idx : ∀ i : Fin r, ∃ (idx : ℕ) (hidx : idx < tags.length), tags[idx]'hidx = Sum.inl i :=
      fun i => List.mem_iff_getElem.mp (mem_buildTags_inl hasRoot i)
    obtain ⟨j, hj_le_r, hinl_lt_j⟩ := buildTags_enclosingCell hasRoot m
    -- Both x1 and x2 lie in cell j of rs1 and rs2!
    have hx1_in : inCell rs1 j x1 := by
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · obtain ⟨idx, hidx, htag⟩ := hinl_idx ⟨j - 1, h2⟩
        have hlt_m : idx < m := (hinl_lt_j ⟨j - 1, h2⟩ idx hidx htag).mpr (show j - 1 < j by omega)
        have hm1_lt : m - 1 < tags.length := by omega
        have hx1_gt := hx1.1 (by omega) (hlen1.symm ▸ hm1_lt)
        rw [hget1 (m - 1) hm1_lt] at hx1_gt
        have hle : eval1 (tags[idx]'hidx) ≤ eval1 (tags[m - 1]'hm1_lt) := by
          rcases eq_or_lt_of_le (show idx ≤ m - 1 by omega) with heq | hlt
          · simp [heq]
          · exact le_of_lt (heval1_lt _ (List.getElem_mem hidx) _ (List.getElem_mem _)
              (List.pairwise_iff_getElem.mp htags_pw idx (m - 1) hidx hm1_lt hlt))
        have heq1 : eval1 (tags[idx]'hidx) = rs1[j - 1]'h2 := by rw [htag]
        exact lt_of_le_of_lt (heq1 ▸ hle) hx1_gt
      · obtain ⟨idx, hidx, htag⟩ := hinl_idx ⟨j, h3⟩
        have hge_m : m ≤ idx := not_lt.mp (mt (hinl_lt_j ⟨j, h3⟩ idx hidx htag).mp (lt_irrefl j))
        have hm_lt : m < tags.length := lt_of_le_of_lt hge_m hidx
        have hx1_lt := hx1.2 (hlen1.symm ▸ hm_lt)
        rw [hget1 m hm_lt] at hx1_lt
        have hle : eval1 (tags[m]'hm_lt) ≤ eval1 (tags[idx]'hidx) := by
          rcases eq_or_lt_of_le hge_m with heq | hlt
          · simp [heq]
          · exact le_of_lt (heval1_lt _ (List.getElem_mem _) _ (List.getElem_mem hidx)
              (List.pairwise_iff_getElem.mp htags_pw m idx hm_lt hidx hlt))
        have heq1 : eval1 (tags[idx]'hidx) = rs1[j]'h3 := by rw [htag]
        exact lt_of_lt_of_le hx1_lt (heq1 ▸ hle)
    have hx2_in : inCell rs2 j x2 := by
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · have h2' : j - 1 < r := hr2 ▸ h2
        obtain ⟨idx, hidx, htag⟩ := hinl_idx ⟨j - 1, h2'⟩
        have hlt_m : idx < m := (hinl_lt_j ⟨j - 1, h2'⟩ idx hidx htag).mpr (show j - 1 < j by omega)
        have hm1_lt : m - 1 < tags.length := by omega
        have hx2_gt := hx2.1 (by omega) (hlen2.symm ▸ hm1_lt)
        rw [hget2 (m - 1) hm1_lt] at hx2_gt
        have hle : eval2 (tags[idx]'hidx) ≤ eval2 (tags[m - 1]'hm1_lt) := by
          rcases eq_or_lt_of_le (show idx ≤ m - 1 by omega) with heq | hlt
          · simp [heq]
          · exact le_of_lt (heval2_lt _ (List.getElem_mem hidx) _ (List.getElem_mem _)
              (List.pairwise_iff_getElem.mp htags_pw idx (m - 1) hidx hm1_lt hlt))
        have heq1 : eval2 (tags[idx]'hidx) = rs2[j - 1]'h2 := by rw [htag]
        exact lt_of_le_of_lt (heq1 ▸ hle) hx2_gt
      · have h3' : j < r := hr2 ▸ h3
        obtain ⟨idx, hidx, htag⟩ := hinl_idx ⟨j, h3'⟩
        have hge_m : m ≤ idx := not_lt.mp (mt (hinl_lt_j ⟨j, h3'⟩ idx hidx htag).mp (lt_irrefl j))
        have hm_lt : m < tags.length := lt_of_le_of_lt hge_m hidx
        have hx2_lt := hx2.2 (hlen2.symm ▸ hm_lt)
        rw [hget2 m hm_lt] at hx2_lt
        have hle : eval2 (tags[m]'hm_lt) ≤ eval2 (tags[idx]'hidx) := by
          rcases eq_or_lt_of_le hge_m with heq | hlt
          · simp [heq]
          · exact le_of_lt (heval2_lt _ (List.getElem_mem _) _ (List.getElem_mem hidx)
              (List.pairwise_iff_getElem.mp htags_pw m idx hm_lt hidx hlt))
        have heq1 : eval2 (tags[idx]'hidx) = rs2[j]'h3 := by rw [htag]
        exact lt_of_lt_of_le hx2_lt (heq1 ▸ hle)
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · change rsign (P1.eval x1) = rsign (P2.eval x2)
      let jF : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj_le_r⟩
      by_cases hhr : hasRoot jF = true
      · obtain ⟨pos, hpos, htag_pos⟩ :=
          List.mem_iff_getElem.mp ((mem_buildTags_inr hasRoot jF).mpr hhr)
        rcases le_or_gt m pos with hmp | hpm
        · -- Both x1 < ξ1 jF and x2 < ξ2 jF
          have hm_lt : m < tags.length := lt_of_le_of_lt hmp hpos
          have h1lt : x1 < ξ1 jF := by
            have hx1_lt := hx1.2 (hlen1.symm ▸ hm_lt)
            rw [hget1 m hm_lt] at hx1_lt
            have hle : eval1 (tags[m]'hm_lt) ≤ eval1 (tags[pos]'hpos) := by
              rcases eq_or_lt_of_le hmp with rfl | hlt
              · exact le_rfl
              · exact le_of_lt (heval1_lt _ (List.getElem_mem _) _ (List.getElem_mem hpos)
                  (List.pairwise_iff_getElem.mp htags_pw m pos hm_lt hpos hlt))
            rw [htag_pos] at hle
            exact lt_of_lt_of_le hx1_lt hle
          have h2lt : x2 < ξ2 jF := by
            have hx2_lt := hx2.2 (hlen2.symm ▸ hm_lt)
            rw [hget2 m hm_lt] at hx2_lt
            have hle : eval2 (tags[m]'hm_lt) ≤ eval2 (tags[pos]'hpos) := by
              rcases eq_or_lt_of_le hmp with rfl | hlt
              · exact le_rfl
              · exact le_of_lt (heval2_lt _ (List.getElem_mem _) _ (List.getElem_mem hpos)
                  (List.pairwise_iff_getElem.mp htags_pw m pos hm_lt hpos hlt))
            rw [htag_pos] at hle
            exact lt_of_lt_of_le hx2_lt hle
          rw [((hdic1 jF).2.2.1 (ξ1 jF) (hξ1_spec jF hhr).1 (hξ1_spec jF hhr).2).1 x1 hx1_in h1lt,
              ((hdic2 jF).2.2.1 (ξ2 jF) (hξ2_spec jF hhr).1 (hξ2_spec jF hhr).2).1 x2 hx2_in h2lt]
          exact hsL_eq jF
        · -- Both ξ1 jF < x1 and ξ2 jF < x2
          have hm1_lt : m - 1 < tags.length := by omega
          have h1gt : ξ1 jF < x1 := by
            have hx1_gt := hx1.1 (by omega) (hlen1.symm ▸ hm1_lt)
            rw [hget1 (m - 1) hm1_lt] at hx1_gt
            have hle : eval1 (tags[pos]'hpos) ≤ eval1 (tags[m - 1]'hm1_lt) := by
              rcases eq_or_lt_of_le (show pos ≤ m - 1 by omega) with heq | hlt
              · simp [heq]
              · exact le_of_lt (heval1_lt _ (List.getElem_mem hpos) _ (List.getElem_mem _)
                  (List.pairwise_iff_getElem.mp htags_pw pos (m - 1) hpos hm1_lt hlt))
            rw [htag_pos] at hle
            exact lt_of_le_of_lt hle hx1_gt
          have h2gt : ξ2 jF < x2 := by
            have hx2_gt := hx2.1 (by omega) (hlen2.symm ▸ hm1_lt)
            rw [hget2 (m - 1) hm1_lt] at hx2_gt
            have hle : eval2 (tags[pos]'hpos) ≤ eval2 (tags[m - 1]'hm1_lt) := by
              rcases eq_or_lt_of_le (show pos ≤ m - 1 by omega) with heq | hlt
              · simp [heq]
              · exact le_of_lt (heval2_lt _ (List.getElem_mem hpos) _ (List.getElem_mem _)
                  (List.pairwise_iff_getElem.mp htags_pw pos (m - 1) hpos hm1_lt hlt))
            rw [htag_pos] at hle
            exact lt_of_le_of_lt hle hx2_gt
          rw [((hdic1 jF).2.2.1 (ξ1 jF) (hξ1_spec jF hhr).1 (hξ1_spec jF hhr).2).2 x1 hx1_in h1gt,
              ((hdic2 jF).2.2.1 (ξ2 jF) (hξ2_spec jF hhr).1 (hξ2_spec jF hhr).2).2 x2 hx2_in h2gt]
          exact hsR_eq jF
      · -- Neither P1 nor P2 has a root in cell j
        have hno1 : ∀ ξ, inCell rs1 j ξ → P1.eval ξ ≠ 0 := fun ξ hξ hP =>
          hhr ((hex1 jF).mpr ⟨ξ, hξ, hP⟩)
        have hno2 : ∀ ξ, inCell rs2 j ξ → P2.eval ξ ≠ 0 := fun ξ hξ hP =>
          hhr ((hex2 jF).mpr ⟨ξ, hξ, hP⟩)
        rw [(hdic1 jF).2.2.2 hno1 x1 hx1_in, (hdic2 jF).2.2.2 hno2 x2 hx2_in]
        change (if cellLeftSign P1 rs1 jF.val ≠ .zero then cellLeftSign P1 rs1 jF.val else ε jF) =
          (if cellLeftSign P2 rs2 jF.val ≠ .zero then cellLeftSign P2 rs2 jF.val else ε jF)
        rw [hsL_eq jF]
    · exact hST.at_cells j hj_le_r x1 x2 hx1_in hx2_in q hqS

/-! #### Hörmander's Lemma (uniform univariate sign-table elimination over any commutative ring `A`) -/

lemma hormander_lemma {A : Type*} [CommRing A] :
    ∀ (d c : ℕ) (F : Finset (Polynomial A)),
      (∀ p ∈ F, p.natDegree ≤ d) →
      (F.filter (fun p => p.natDegree = d)).card ≤ c →
      ∃ G : Finset A, ∀ {R₁ R₂ : Type}
        [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁] [HasPolyIVT R₁]
        [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂] [HasPolyIVT R₂]
        (φ₁ : A →+* R₁) (φ₂ : A →+* R₂),
        (∀ g ∈ G, rsign (φ₁ g) = rsign (φ₂ g)) →
        SameSignTable F φ₁ φ₂ := by
  classical
  intro d
  induction d with
  | zero =>
    intro c F hdeg _
    refine ⟨F.image (fun p => p.coeff 0), ?_⟩
    intro R₁ R₂ _ _ _ _ _ _ _ _ φ₁ φ₂ hG
    have hconst : ∀ (R : Type) [Field R] [LinearOrder R] (φ : A →+* R),
        rootList (F.image (Polynomial.map φ)) = [] := by
      intro R _ _ φ
      apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _) List.Pairwise.nil
      intro x
      rw [mem_rootList]
      simp only [List.not_mem_nil, iff_false, not_exists, not_and]
      intro q hq hq0 hqx
      obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hq
      have hp0 : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (hdeg p hpF))
      rw [hp0, Polynomial.map_C] at hq0 hqx
      simp only [Polynomial.eval_C] at hqx
      exact hq0 (by rw [hqx, map_zero])
    refine ⟨by rw [hconst, hconst]; rfl, fun i h1 => by rw [hconst] at h1; simp at h1, ?_⟩
    intro j _ x1 x2 _ _ p hp
    have hp0 : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (hdeg p hp))
    rw [hp0, Polynomial.map_C, Polynomial.map_C, Polynomial.eval_C, Polynomial.eval_C]
    exact hG (p.coeff 0) (Finset.mem_image_of_mem _ hp)
  | succ d ih_d =>
    intro c
    induction c with
    | zero =>
      intro F hdeg hcard
      have hdeg' : ∀ p ∈ F, p.natDegree ≤ d := by
        intro p hp
        have hne : p.natDegree ≠ d + 1 := by
          intro heq
          have hmem : p ∈ F.filter (fun p => p.natDegree = d + 1) :=
            Finset.mem_filter.mpr ⟨hp, heq⟩
          have := Finset.card_pos.mpr ⟨p, hmem⟩
          omega
        have := hdeg p hp
        omega
      exact ih_d (F.filter (fun p => p.natDegree = d)).card F hdeg' le_rfl
    | succ c ih_c =>
      intro F hdeg hcard
      by_cases hex : (F.filter (fun p => p.natDegree = d + 1)).Nonempty
      · obtain ⟨p, hp_filt⟩ := hex
        have hpF : p ∈ F := (Finset.mem_filter.mp hp_filt).1
        have hp_deg : p.natDegree = d + 1 := (Finset.mem_filter.mp hp_filt).2
        let F_base : Finset (Polynomial A) := F.erase p
        let p_trunc : Polynomial A := truncPoly p d
        let p' : Polynomial A := p.derivative
        let R0_set : Finset (Polynomial A) :=
          if 1 ≤ d then {pseudoRem p p' d} else ∅
        let Rq_set : Finset (Polynomial A) :=
          F_base.biUnion fun q =>
            (Finset.Icc 1 q.natDegree).image fun k => pseudoRem p (truncPoly q k) k
        let C_set : Finset (Polynomial A) :=
          F.biUnion fun q =>
            (Finset.range (q.natDegree + 1)).image fun k => Polynomial.C (q.coeff k)
        let F' : Finset (Polynomial A) :=
          insert p_trunc (insert p' (F_base ∪ R0_set ∪ Rq_set ∪ C_set))
        -- Verify degree bounds and strictly smaller count of degree-(d+1) elements in F'
        have hp_trunc_deg : p_trunc.natDegree ≤ d := natDegree_truncPoly_le p d
        have hp'_deg : p'.natDegree ≤ d := by
          dsimp only [p']; have := Polynomial.natDegree_derivative_le (p := p); omega
        have hR0_deg : ∀ r ∈ R0_set, r.natDegree ≤ d := by
          intro r hr
          dsimp [R0_set] at hr
          split_ifs at hr with hd1
          · simp only [Finset.mem_singleton] at hr; subst hr
            have := (pseudoRem_spec p p' d hd1 hp'_deg).1; omega
          · simp at hr
        have hRq_deg : ∀ r ∈ Rq_set, r.natDegree ≤ d := by
          intro r hr
          rw [Finset.mem_biUnion] at hr; obtain ⟨q, hqB, hr⟩ := hr
          rw [Finset.mem_image] at hr; obtain ⟨k, hk, rfl⟩ := hr
          rw [Finset.mem_Icc] at hk
          have hqd : q.natDegree ≤ d + 1 := hdeg q (Finset.mem_of_mem_erase hqB)
          have hlt := (pseudoRem_spec p (truncPoly q k) k hk.1 (natDegree_truncPoly_le q k)).1
          omega
        have hC_deg : ∀ r ∈ C_set, r.natDegree ≤ d := by
          intro r hr
          rw [Finset.mem_biUnion] at hr; obtain ⟨q, _, hr⟩ := hr
          rw [Finset.mem_image] at hr; obtain ⟨k, _, rfl⟩ := hr
          simp
        have hF'_deg : ∀ q ∈ F', q.natDegree ≤ d + 1 := by
          intro q hq
          simp only [F', Finset.mem_insert, Finset.mem_union] at hq
          rcases hq with rfl | rfl | (((hq | hq) | hq) | hq)
          · omega
          · omega
          · exact hdeg q (Finset.mem_of_mem_erase hq)
          · have := hR0_deg q hq; omega
          · have := hRq_deg q hq; omega
          · have := hC_deg q hq; omega
        have hF'_card : (F'.filter (fun q => q.natDegree = d + 1)).card ≤ c := by
          have hsub : F'.filter (fun q => q.natDegree = d + 1) ⊆
              (F.filter (fun q => q.natDegree = d + 1)).erase p := by
            intro q hq
            rw [Finset.mem_filter] at hq
            obtain ⟨hqF', hqdeg⟩ := hq
            simp only [F', Finset.mem_insert, Finset.mem_union] at hqF'
            rcases hqF' with rfl | rfl | (((hq | hq) | hq) | hq)
            · omega
            · omega
            · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hq).1,
                Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hq, hqdeg⟩⟩
            · have := hR0_deg q hq; omega
            · have := hRq_deg q hq; omega
            · have := hC_deg q hq; omega
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hp_filt] at h1
          omega
        obtain ⟨G, hG⟩ := ih_c F' hF'_deg hF'_card
        refine ⟨G, ?_⟩
        intro R₁ R₂ _ _ _ _ _ _ _ _ φ₁ φ₂ hGeq
        have hST' : SameSignTable F' φ₁ φ₂ := hG φ₁ φ₂ hGeq
        have hcoeff_eq : ∀ q ∈ F, ∀ k ≤ q.natDegree, rsign (φ₁ (q.coeff k)) = rsign (φ₂ (q.coeff k)) := by
          intro q hq k hk
          have hmem : Polynomial.C (q.coeff k) ∈ F' := by
            simp only [F', Finset.mem_insert, Finset.mem_union]
            right; right; right
            rw [Finset.mem_biUnion]
            exact ⟨q, hq, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩⟩
          obtain ⟨x1, hx1⟩ := exists_inCell (rootList_pairwise (F'.image (Polynomial.map φ₁))) (Nat.zero_le _)
          obtain ⟨x2, hx2⟩ := exists_inCell (rootList_pairwise (F'.image (Polynomial.map φ₂))) (Nat.zero_le _)
          have := hST'.at_cells 0 (Nat.zero_le _) x1 x2 hx1 hx2 _ hmem
          simpa using this
        have hF_eq : F = insert p F_base := (Finset.insert_erase hpF).symm
        by_cases hlead0 : φ₁ (p.coeff (d + 1)) = 0
        · -- Case 1: leading coefficient of p vanishes at both φ₁ and φ₂
          have hlead0_2 : φ₂ (p.coeff (d + 1)) = 0 := by
            rw [← rsign_zero_iff, ← hcoeff_eq p hpF (d + 1) (by omega), rsign_zero_iff]
            exact hlead0
          have hp_eq1 : p.map φ₁ = p_trunc.map φ₁ := by
            symm; apply map_truncPoly_eq
            rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
            intro m hm
            rw [Polynomial.coeff_map]
            by_cases hmd : m = d + 1
            · subst hmd; exact hlead0
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
          have hp_eq2 : p.map φ₂ = p_trunc.map φ₂ := by
            symm; apply map_truncPoly_eq
            rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
            intro m hm
            rw [Polynomial.coeff_map]
            by_cases hmd : m = d + 1
            · subst hmd; exact hlead0_2
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
          have hsub_t : insert p_trunc F_base ⊆ F' := by
            intro q hq
            simp only [F', Finset.mem_insert, Finset.mem_union] at hq ⊢
            rcases hq with rfl | hq
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl hq))))
          have hST_t : SameSignTable (insert p_trunc F_base) φ₁ φ₂ := hST'.mono hsub_t
          have himg1 : F.image (Polynomial.map φ₁) = (insert p_trunc F_base).image (Polynomial.map φ₁) := by
            rw [hF_eq, Finset.image_insert, Finset.image_insert, hp_eq1]
          have himg2 : F.image (Polynomial.map φ₂) = (insert p_trunc F_base).image (Polynomial.map φ₂) := by
            rw [hF_eq, Finset.image_insert, Finset.image_insert, hp_eq2]
          refine ⟨by rw [himg1, himg2]; exact hST_t.len_eq, ?_, ?_⟩
          · intro i h1 h2 q hq
            rw [hF_eq] at hq
            rcases Finset.mem_insert.mp hq with rfl | hqB
            · rw [hp_eq1, hp_eq2]
              simpa only [himg1, himg2] using
                hST_t.at_roots i (by simpa [himg1] using h1) (by simpa [himg2] using h2)
                  p_trunc (Finset.mem_insert_self _ _)
            · simpa only [himg1, himg2] using
                hST_t.at_roots i (by simpa [himg1] using h1) (by simpa [himg2] using h2)
                  q (Finset.mem_insert_of_mem hqB)
          · intro j hj x1 x2 hx1 hx2 q hq
            rw [hF_eq] at hq
            rcases Finset.mem_insert.mp hq with rfl | hqB
            · rw [hp_eq1, hp_eq2]
              exact hST_t.at_cells j (by simpa [himg1] using hj) x1 x2
                (by simpa [himg1] using hx1) (by simpa [himg2] using hx2)
                p_trunc (Finset.mem_insert_self _ _)
            · exact hST_t.at_cells j (by simpa [himg1] using hj) x1 x2
                (by simpa [himg1] using hx1) (by simpa [himg2] using hx2)
                q (Finset.mem_insert_of_mem hqB)
        · -- Case 2: leading coefficient of p is nonzero at both φ₁ and φ₂
          have hlead_ne2 : φ₂ (p.coeff (d + 1)) ≠ 0 := by
            intro h0
            apply hlead0
            rw [← rsign_zero_iff, hcoeff_eq p hpF (d + 1) (by omega), rsign_zero_iff]
            exact h0
          have hdeg1_eq : (p.map φ₁).natDegree = d + 1 := by
            apply le_antisymm
            · exact (Polynomial.natDegree_map_le (f := φ₁) (p := p)).trans (by omega)
            · apply Polynomial.le_natDegree_of_ne_zero
              rw [Polynomial.coeff_map]; exact hlead0
          have hdeg2_eq : (p.map φ₂).natDegree = d + 1 := by
            apply le_antisymm
            · exact (Polynomial.natDegree_map_le (f := φ₂) (p := p)).trans (by omega)
            · apply Polynomial.le_natDegree_of_ne_zero
              rw [Polynomial.coeff_map]; exact hlead_ne2
          have hlc_eq : rsign (p.map φ₁).leadingCoeff = rsign (p.map φ₂).leadingCoeff := by
            rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hdeg1_eq, hdeg2_eq,
              Polynomial.coeff_map, Polynomial.coeff_map]
            exact hcoeff_eq p hpF (d + 1) (by omega)
          have hsub_S : insert p' F_base ⊆ F' := by
            intro q hq
            simp only [F', Finset.mem_insert, Finset.mem_union] at hq ⊢
            rcases hq with rfl | hq
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl hq))))
          have hST_S : SameSignTable (insert p' F_base) φ₁ φ₂ := hST'.mono hsub_S
          -- Prove signs of p match at every root of insert p' F_base
          have hat_roots : ∀ (i : ℕ)
              (h1 : i < (rootList ((insert p' F_base).image (Polynomial.map φ₁))).length)
              (h2 : i < (rootList ((insert p' F_base).image (Polynomial.map φ₂))).length),
              rsign ((p.map φ₁).eval ((rootList ((insert p' F_base).image (Polynomial.map φ₁)))[i]'h1)) =
              rsign ((p.map φ₂).eval ((rootList ((insert p' F_base).image (Polynomial.map φ₂)))[i]'h2)) := by
            intro i h1 h2
            let x1 := (rootList ((insert p' F_base).image (Polynomial.map φ₁)))[i]'h1
            let x2 := (rootList ((insert p' F_base).image (Polynomial.map φ₂)))[i]'h2
            -- Locate x1 and x2 at the SAME index in rootList (F'.image (map φ))!
            -- Even simpler: use SameSignTable.mono? Wait: find which polynomial in insert p' F_base vanishes at x1!
            obtain ⟨_, hqm, hq0, hqx1⟩ := (mem_rootList _ x1).mp (List.getElem_mem h1)
            obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hqm
            -- Also q.map φ₂ vanishes at x2!
            have hqx2 : (q.map φ₂).eval x2 = 0 := by
              rw [← rsign_zero_iff, ← hST_S.at_roots i h1 h2 q hqS, rsign_zero_iff]
              exact hqx1
            -- To compare R(x1) and R(x2) for the pseudo-remainder R ∈ F', observe x1 ∈ rootList (F'...) and
            -- apply SameSignTable.mono to insert R (insert p' F_base) ⊆ F'!
            have hcmp_rem : ∀ (R : Polynomial A), R ∈ F' →
                rsign ((R.map φ₁).eval x1) = rsign ((R.map φ₂).eval x2) := by
              intro R hRF'
              -- x1 is a root of q.map φ₁ in S ⊆ F', wait: find the common index in F'!
              -- Wait: we can prove a direct 10-line lemma: if S ⊆ F' and SameSignTable F' φ₁ φ₂,
              -- then at the i-th root of S, ALL polynomials in F' have equal sign!
              -- Let's prove it right here!
              let rs1' := rootList (F'.image (Polynomial.map φ₁))
              let rs2' := rootList (F'.image (Polynomial.map φ₂))
              let L := rs1'.length
              have hL : rs2'.length = L := hST'.len_eq.symm
              let keep : Fin L → Bool := fun idx =>
                decide (∃ r ∈ insert p' F_base, r.map φ₁ ≠ 0 ∧ (r.map φ₁).eval (rs1'[idx.val]'idx.isLt) = 0)
              have hkeep2 : ∀ idx : Fin L, keep idx = true ↔
                  ∃ r ∈ insert p' F_base, r.map φ₂ ≠ 0 ∧ (r.map φ₂).eval (rs2'[idx.val]'(hL.symm ▸ idx.isLt)) = 0 := by
                intro idx; simp only [keep, decide_eq_true_eq]
                constructor <;> rintro ⟨r, hr, hne, hev⟩
                · exact ⟨r, hr, mt (hST'.map_eq_zero_iff (hsub_S hr)).mpr hne, by
                    rw [← rsign_zero_iff, ← hST'.at_roots idx.val idx.isLt (hL.symm ▸ idx.isLt) r (hsub_S hr),
                      rsign_zero_iff]; exact hev⟩
                · exact ⟨r, hr, mt (hST'.map_eq_zero_iff (hsub_S hr)).mp hne, by
                    rw [← rsign_zero_iff, hST'.at_roots idx.val idx.isLt (hL.symm ▸ idx.isLt) r (hsub_S hr),
                      rsign_zero_iff]; exact hev⟩
              let idxs : List (Fin L) := (List.finRange L).filter (fun idx => keep idx)
              have hidxs_pw : idxs.Pairwise (· < ·) := (List.pairwise_lt_finRange L).filter _
              have heq1 : rootList ((insert p' F_base).image (Polynomial.map φ₁)) =
                  idxs.map (fun idx => rs1'[idx.val]'idx.isLt) := by
                apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _)
                  (List.pairwise_map.mpr (hidxs_pw.imp fun h => pairwise_lt_get (rootList_pairwise _) _ _ h))
                intro y; rw [mem_rootList]
                constructor
                · rintro ⟨_, hym, hy0, hyx⟩
                  obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hym
                  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp
                    ((mem_rootList _ y).mpr ⟨r.map φ₁, Finset.mem_image_of_mem _ (hsub_S hrS), hy0, hyx⟩)
                  exact List.mem_map.mpr ⟨⟨idx, hidx⟩, List.mem_filter.mpr
                    ⟨List.mem_finRange _, decide_eq_true ⟨r, hrS, hy0, hyx⟩⟩, rfl⟩
                · intro hy; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hy
                  obtain ⟨r, hrS, hr0, hrx⟩ := of_decide_eq_true (List.mem_filter.mp hidx).2
                  exact ⟨r.map φ₁, Finset.mem_image_of_mem _ hrS, hr0, hrx⟩
              have heq2 : rootList ((insert p' F_base).image (Polynomial.map φ₂)) =
                  idxs.map (fun idx => rs2'[idx.val]'(hL.symm ▸ idx.isLt)) := by
                apply list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise _)
                  (List.pairwise_map.mpr (hidxs_pw.imp fun {a b} h =>
                    pairwise_lt_get (rootList_pairwise (F'.image (Polynomial.map φ₂)))
                      (hL.symm ▸ a.isLt) (hL.symm ▸ b.isLt) h))
                intro y; rw [mem_rootList]
                constructor
                · rintro ⟨_, hym, hy0, hyx⟩
                  obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hym
                  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp
                    ((mem_rootList _ y).mpr ⟨r.map φ₂, Finset.mem_image_of_mem _ (hsub_S hrS), hy0, hyx⟩)
                  exact List.mem_map.mpr ⟨⟨idx, hL ▸ hidx⟩, List.mem_filter.mpr
                    ⟨List.mem_finRange _, (hkeep2 ⟨idx, hL ▸ hidx⟩).mpr ⟨r, hrS, hy0, hyx⟩⟩, rfl⟩
                · intro hy; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hy
                  obtain ⟨r, hrS, hr0, hrx⟩ := (hkeep2 idx).mp (List.mem_filter.mp hidx).2
                  exact ⟨r.map φ₂, Finset.mem_image_of_mem _ hrS, hr0, hrx⟩
              have hi' : i < idxs.length := by rw [heq1] at h1; simpa using h1
              have hx1_eq : x1 = rs1'[(idxs[i]'hi').val]'(idxs[i]'hi').isLt := by
                simp only [x1, heq1, List.getElem_map]
              have hx2_eq : x2 = rs2'[(idxs[i]'hi').val]'(hL.symm ▸ (idxs[i]'hi').isLt) := by
                simp only [x2, heq2, List.getElem_map]
              rw [hx1_eq, hx2_eq]
              exact hST'.at_roots (idxs[i]'hi').val (idxs[i]'hi').isLt (hL.symm ▸ (idxs[i]'hi').isLt) R hRF'
            rcases Finset.mem_insert.mp hqS with rfl | hqB
            · -- q = p'
              by_cases hd1 : 1 ≤ d
              · have hc1 : φ₁ (p'.coeff d) ≠ 0 := by
                  rw [Polynomial.coeff_derivative, map_mul, map_add, map_natCast, map_one]
                  exact mul_ne_zero hlead0 (by exact_mod_cast Nat.succ_ne_zero d)
                have hc2 : φ₂ (p'.coeff d) ≠ 0 := by
                  rw [Polynomial.coeff_derivative, map_mul, map_add, map_natCast, map_one]
                  exact mul_ne_zero hlead_ne2 (by exact_mod_cast Nat.succ_ne_zero d)
                rw [rsign_eval_pseudoRem φ₁ p p' d hd1 hp'_deg hc1 x1 hqx1,
                    rsign_eval_pseudoRem φ₂ p p' d hd1 hp'_deg hc2 x2 hqx2]
                apply hcmp_rem (pseudoRem p p' d)
                simp only [F', Finset.mem_insert, Finset.mem_union]
                right; right; left; left; right
                simp [R0_set, hd1]
              · -- d = 0, so p' is a nonzero constant, contradiction with p'.map φ₁ having root x1!
                have hd0 : d = 0 := by omega
                have hp'0 : (p'.map φ₁).natDegree = 0 := by
                  have := Polynomial.natDegree_map_le (f := φ₁) (p := p'); omega
                rw [Polynomial.eq_C_of_natDegree_eq_zero hp'0] at hq0 hqx1
                simp only [Polynomial.eval_C] at hqx1
                exact absurd (by rw [hqx1, map_zero]) hq0
            · -- q ∈ F_base
              let k := (q.map φ₁).natDegree
              have hqF : q ∈ F := Finset.mem_of_mem_erase hqB
              have hk_pos : 1 ≤ k := by
                by_contra h0
                have hk0 : (q.map φ₁).natDegree = 0 := by omega
                rw [Polynomial.eq_C_of_natDegree_eq_zero hk0] at hq0 hqx1
                simp only [Polynomial.eval_C] at hqx1
                exact hq0 (by rw [hqx1, map_zero])
              have hk_le : k ≤ q.natDegree := Polynomial.natDegree_map_le (f := φ₁) (p := q)
              have hc1 : φ₁ (q.coeff k) ≠ 0 := by
                rw [← Polynomial.coeff_map]
                exact Polynomial.leadingCoeff_ne_zero.mpr hq0
              have hc2 : φ₂ (q.coeff k) ≠ 0 := by
                intro h0
                apply hc1
                rw [← rsign_zero_iff, hcoeff_eq q hqF k hk_le, rsign_zero_iff]
                exact h0
              have hk2_le : (q.map φ₂).natDegree ≤ k := by
                rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
                intro m hm
                rw [Polynomial.coeff_map]
                by_cases hmq : m ≤ q.natDegree
                · rw [← rsign_zero_iff, ← hcoeff_eq q hqF m hmq, rsign_zero_iff, ← Polynomial.coeff_map]
                  exact Polynomial.coeff_eq_zero_of_natDegree_lt hm
                · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
              have htr1 : (truncPoly q k).map φ₁ = q.map φ₁ := map_truncPoly_eq φ₁ q k le_rfl
              have htr2 : (truncPoly q k).map φ₂ = q.map φ₂ := map_truncPoly_eq φ₂ q k hk2_le
              have hcoeff_tr : (truncPoly q k).coeff k = q.coeff k := by rw [coeff_truncPoly, if_pos le_rfl]
              rw [rsign_eval_pseudoRem φ₁ p (truncPoly q k) k hk_pos (natDegree_truncPoly_le q k)
                    (hcoeff_tr ▸ hc1) x1 (htr1.symm ▸ hqx1),
                  rsign_eval_pseudoRem φ₂ p (truncPoly q k) k hk_pos (natDegree_truncPoly_le q k)
                    (hcoeff_tr ▸ hc2) x2 (htr2.symm ▸ hqx2)]
              apply hcmp_rem (pseudoRem p (truncPoly q k) k)
              simp only [F', Finset.mem_insert, Finset.mem_union]
              right; right; left; right
              rw [Finset.mem_biUnion]
              exact ⟨q, hqB, Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, rfl⟩⟩
          have hST_ins := hST_S.insert_poly (by omega) (by omega) (hdeg1_eq.trans hdeg2_eq.symm)
            hlc_eq hat_roots
          have hsub_F : F ⊆ insert p (insert p' F_base) := by
            rw [hF_eq]
            intro q hq
            rcases Finset.mem_insert.mp hq with rfl | hqB
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hqB)
          exact hST_ins.mono hsub_F
      · -- No polynomial of degree d + 1 in F
        have hdeg' : ∀ p ∈ F, p.natDegree ≤ d := by
          intro p hp
          have hne : p.natDegree ≠ d + 1 := fun heq => hex ⟨p, Finset.mem_filter.mpr ⟨hp, heq⟩⟩
          have := hdeg p hp; omega
        exact ih_d (F.filter (fun p => p.natDegree = d)).card F hdeg' le_rfl

lemma eval₂_finSuccEquiv {n : ℕ} {R : Type*} [CommRing R] (ι : ℝ →+* R) (x : Fin (n + 1) → R)
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    ((MvPolynomial.finSuccEquiv ℝ n p).map (MvPolynomial.eval₂Hom ι (Fin.tail x))).eval (x 0) =
      MvPolynomial.eval₂ ι x p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, MvPolynomial.eval₂_mul, hp]
    congr 1
    refine Fin.cases ?_ ?_ i
    · rw [MvPolynomial.finSuccEquiv_X_zero]; simp
    · intro j; rw [MvPolynomial.finSuccEquiv_X_succ]; simp [Fin.tail]

lemma tarski_seidenberg_transfer {n : ℕ} {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [HasPolyIVT R] (ι : ℝ →+* R)
    (P : Finset (MvPolynomial (Fin n) ℝ)) (x : Fin n → R) :
    ∃ x0 : Fin n → ℝ, ∀ p ∈ P,
      (0 < MvPolynomial.eval x0 p ↔ 0 < MvPolynomial.eval₂ ι x p) ∧
      (MvPolynomial.eval x0 p = 0 ↔ MvPolynomial.eval₂ ι x p = 0) := by
  suffices ∀ (n : ℕ) (P : Finset (MvPolynomial (Fin n) ℝ)) (x : Fin n → R),
      ∃ x0 : Fin n → ℝ, ∀ p ∈ P,
        rsign (MvPolynomial.eval x0 p) = rsign (MvPolynomial.eval₂ ι x p) by
    obtain ⟨x0, hx0⟩ := this n P x
    refine ⟨x0, fun p hp => ?_⟩
    have hs := hx0 p hp
    exact ⟨by rw [← rsign_pos_iff, ← rsign_pos_iff, hs],
      by rw [← rsign_zero_iff, ← rsign_zero_iff, hs]⟩
  intro m
  induction m with
  | zero =>
    intro P x
    have hconst0 : ∀ q : MvPolynomial (Fin 0) ℝ, q = MvPolynomial.C (MvPolynomial.eval Fin.elim0 q) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C r => simp
      | add a b ha hb => rw [map_add, map_add, ← ha, ← hb]
      | mul_X a i _ => exact Fin.elim0 i
    refine ⟨Fin.elim0, fun p _ => ?_⟩
    conv_rhs => rw [hconst0 p]
    rw [MvPolynomial.eval₂_C]
    exact (rsign_real_hom ι (MvPolynomial.eval Fin.elim0 p)).symm
  | succ m ih =>
    intro P x
    classical
    let F : Finset (Polynomial (MvPolynomial (Fin m) ℝ)) := P.image (MvPolynomial.finSuccEquiv ℝ m)
    let d : ℕ := F.sup Polynomial.natDegree
    have hdeg : ∀ q ∈ F, q.natDegree ≤ d := fun q hq => Finset.le_sup hq
    obtain ⟨G, hG⟩ := hormander_lemma d F.card F hdeg (Finset.card_filter_le _ _)
    obtain ⟨a0, ha0⟩ := ih G (Fin.tail x)
    let φ₁ : MvPolynomial (Fin m) ℝ →+* ℝ := MvPolynomial.eval₂Hom (RingHom.id ℝ) a0
    let φ₂ : MvPolynomial (Fin m) ℝ →+* R := MvPolynomial.eval₂Hom ι (Fin.tail x)
    have hGeq : ∀ g ∈ G, rsign (φ₁ g) = rsign (φ₂ g) := fun g hg => ha0 g hg
    have hST : SameSignTable F φ₁ φ₂ := hG φ₁ φ₂ hGeq
    obtain ⟨t0, ht0⟩ := hST.realize (x 0)
    refine ⟨Fin.cons t0 a0, fun p hp => ?_⟩
    have h1 : MvPolynomial.eval (Fin.cons t0 a0) p =
        (((MvPolynomial.finSuccEquiv ℝ m p).map φ₁).eval t0) := by
      have hev := eval₂_finSuccEquiv (RingHom.id ℝ) (Fin.cons t0 a0) p
      rw [Fin.cons_zero, Fin.tail_cons] at hev
      exact hev.symm
    have h2 : MvPolynomial.eval₂ ι x p =
        (((MvPolynomial.finSuccEquiv ℝ m p).map φ₂).eval (x 0)) :=
      (eval₂_finSuccEquiv ι x p).symm
    rw [h1, h2]
    exact ht0 _ (Finset.mem_image_of_mem _ hp)

end StenglePsatz

theorem solution {n s t u : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ) (h : Fin u → MvPolynomial (Fin n) ℝ)
    (hempty : psatzSet f g h = ∅) :
    ∃ F ∈ cone (Set.range f), ∃ G ∈ Submonoid.closure (Set.range g),
      ∃ H ∈ Ideal.span (Set.range h), F + G ^ 2 + H = 0 := by
  by_contra hno
  obtain ⟨K, _, _, _, ι, x, hf, hg, hh⟩ := StenglePsatz.exists_ordered_field_solution f g h hno
  obtain ⟨R, _, _, _, _, emb, hemb⟩ := StenglePsatz.exists_real_closure K
  let ι' : ℝ →+* R := emb.comp ι
  let x' : Fin n → R := emb ∘ x
  have heval' : ∀ p : MvPolynomial (Fin n) ℝ,
      MvPolynomial.eval₂ ι' x' p = emb (MvPolynomial.eval₂ ι x p) := fun p =>
    (MvPolynomial.hom_eval₂ p ι emb x).symm
  let P : Finset (MvPolynomial (Fin n) ℝ) :=
    Finset.image f Finset.univ ∪ Finset.image g Finset.univ ∪ Finset.image h Finset.univ
  obtain ⟨x0, hx0⟩ := StenglePsatz.tarski_seidenberg_transfer ι' P x'
  have hx0_mem : x0 ∈ psatzSet f g h := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hjP : f j ∈ P := by simp [P]
      have hnonneg : 0 ≤ MvPolynomial.eval₂ ι' x' (f j) := by
        rw [heval']; exact hemb _ (hf j)
      rcases lt_or_eq_of_le hnonneg with hpos | heq
      · exact le_of_lt ((hx0 (f j) hjP).1.mpr hpos)
      · exact le_of_eq ((hx0 (f j) hjP).2.mpr heq.symm).symm
    · intro k hk0
      have hkP : g k ∈ P := by simp [P]
      have hgk' : MvPolynomial.eval₂ ι' x' (g k) = 0 := (hx0 (g k) hkP).2.mp hk0
      rw [heval'] at hgk'
      exact hg k (emb.injective (by simpa using hgk'))
    · intro l
      have hlP : h l ∈ P := by simp [P]
      exact (hx0 (h l) hlP).2.mpr (by rw [heval', hh l, map_zero])
  rw [hempty] at hx0_mem
  exact hx0_mem
