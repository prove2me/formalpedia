-- Prove2me | solution 1 for Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b43ba48d-dc2b-5062-ae17-51b0c1e63496

import Mathlib
import Theorems.Thm_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient
import Theorems.Thm_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy

set_option autoImplicit false

namespace P2MBrick

open Submodule

variable {T : Type*} [CommRing T] {G : Type*} [AddCommGroup G] [Module T G] (q : ℕ) [hq : Fact q.Prime]

theorem nsmul_eq_nsmul_of_modEq {N a b : ℕ} {y : G} (hy : N • y = 0) (h : a ≡ b [MOD N]) :
    a • y = b • y := by
  have key : ∀ c : ℕ, c • y = (c % N) • y := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c N, add_nsmul, mul_comm, mul_nsmul', hy, nsmul_zero, add_zero]
  rw [key a, key b, h]

variable (T G) in

def qTors : Submodule T G where
  carrier := {x | ∃ n : ℕ, q ^ n • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [nsmul_add, pow_add, mul_comm, mul_nsmul', hn, nsmul_zero, zero_add, mul_comm, mul_nsmul', hm,
      nsmul_zero]
  smul_mem' := by
    rintro t x ⟨n, hn⟩
    exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩

theorem mem_qTors_iff (x : G) : x ∈ qTors T G q ↔ ∃ n : ℕ, q ^ n • x = 0 := Iff.rfl

theorem toZModPow_val_modEq (l : ℤ_[q]) {n m : ℕ} (h : n ≤ m) :
    (PadicInt.toZModPow m l).val ≡ (PadicInt.toZModPow n l).val [MOD q ^ n] := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have e := congrArg (fun f => f l) (PadicInt.zmod_cast_comp_toZModPow n m h)
  simp only [RingHom.coe_comp, Function.comp_apply, ZMod.castHom_apply] at e
  rw [ZMod.cast_eq_val] at e
  rw [e, ZMod.natCast_zmod_val]

open Classical in

noncomputable def lvl (x : qTors T G q) : ℕ := Nat.find x.2

open Classical in
theorem lvl_spec (x : qTors T G q) : q ^ lvl q x • (x : G) = 0 := Nat.find_spec x.2

open Classical in
theorem lvl_le (x : qTors T G q) {m : ℕ} (hm : q ^ m • (x : G) = 0) : lvl q x ≤ m := Nat.find_min' x.2 hm

theorem pow_smul_eq_zero_of_le {x : G} {n m : ℕ} (h : n ≤ m) (hx : q ^ n • x = 0) : q ^ m • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, mul_nsmul', hx, nsmul_zero]

noncomputable def psmul (l : ℤ_[q]) (x : qTors T G q) : qTors T G q :=
  ⟨(PadicInt.toZModPow (lvl q x) l).val • (x : G), by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩⟩

theorem coe_psmul (l : ℤ_[q]) (x : qTors T G q) {m : ℕ} (hm : q ^ m • (x : G) = 0) :
    ((psmul q l x : qTors T G q) : G) = (PadicInt.toZModPow m l).val • (x : G) := by
  show (PadicInt.toZModPow (lvl q x) l).val • (x : G) = _
  have hmin : lvl q x ≤ m := lvl_le q x hm
  exact (nsmul_eq_nsmul_of_modEq (lvl_spec q x) (toZModPow_val_modEq q l hmin)).symm

noncomputable scoped instance : SMul ℤ_[q] (qTors T G q) := ⟨psmul q⟩

private theorem _root_.P2MBrick.smul_def (l : ℤ_[q]) (x : qTors T G q) : l • x = psmul q l x := rfl

p2m_export "P2MBrick" "smul_def"
theorem coe_smul' (l : ℤ_[q]) (x : qTors T G q) {m : ℕ} (hm : q ^ m • (x : G) = 0) :
    ((l • x : qTors T G q) : G) = (PadicInt.toZModPow m l).val • (x : G) := coe_psmul q l x hm

theorem exists_common_level (x y : qTors T G q) :
    ∃ m : ℕ, 0 < m ∧ q ^ m • (x : G) = 0 ∧ q ^ m • (y : G) = 0 := by
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨k, hk⟩ := y.2
  exact ⟨n + k + 1, Nat.succ_pos _, pow_smul_eq_zero_of_le q (by omega) hn,
    pow_smul_eq_zero_of_le q (by omega) hk⟩

theorem pow_smul_coe_smul_eq_zero (l : ℤ_[q]) (x : qTors T G q) {m : ℕ} (hm : q ^ m • (x : G) = 0) :
    q ^ m • ((l • x : qTors T G q) : G) = 0 := by
  rw [coe_smul' q l x hm, smul_comm, hm, smul_zero]

noncomputable scoped instance : Module ℤ_[q] (qTors T G q) where
  one_smul x := by
    obtain ⟨m, hm0, hm, -⟩ := exists_common_level q x x
    apply Subtype.ext
    rw [coe_smul' q 1 x hm, map_one, ZMod.val_one_eq_one_mod]
    rw [nsmul_eq_nsmul_of_modEq hm (Nat.mod_modEq 1 (q ^ m)), one_nsmul]
  mul_smul l l' x := by
    obtain ⟨m, hm0, hm, -⟩ := exists_common_level q x x
    apply Subtype.ext
    have hm' := pow_smul_coe_smul_eq_zero q l' x hm
    rw [coe_smul' q (l * l') x hm, coe_smul' q l (l' • x) hm', coe_smul' q l' x hm, map_mul, ZMod.val_mul,
      ← mul_nsmul']
    exact (nsmul_eq_nsmul_of_modEq hm (Nat.mod_modEq _ _))
  smul_zero l := by
    apply Subtype.ext
    rw [coe_smul' q l 0 (m := 0) (by simp)]
    simp
  smul_add l x y := by
    obtain ⟨m, hm0, hmx, hmy⟩ := exists_common_level q x y
    have hmxy : q ^ m • ((x + y : qTors T G q) : G) = 0 := by
      rw [Submodule.coe_add, nsmul_add, hmx, hmy, add_zero]
    apply Subtype.ext
    rw [Submodule.coe_add, coe_smul' q l _ hmxy, coe_smul' q l x hmx, coe_smul' q l y hmy, Submodule.coe_add,
      nsmul_add]
  add_smul l l' x := by
    obtain ⟨m, hm0, hm, -⟩ := exists_common_level q x x
    apply Subtype.ext
    rw [Submodule.coe_add, coe_smul' q (l + l') x hm, coe_smul' q l x hm, coe_smul' q l' x hm, map_add,
      ZMod.val_add, ← add_nsmul]
    exact (nsmul_eq_nsmul_of_modEq hm (Nat.mod_modEq _ _))
  zero_smul x := by
    apply Subtype.ext
    rw [coe_smul' q 0 x (lvl_spec q x), map_zero, ZMod.val_zero, zero_nsmul, Submodule.coe_zero]

scoped instance : SMulCommClass T ℤ_[q] (qTors T G q) where
  smul_comm t l x := by
    obtain ⟨m, -, hm, -⟩ := exists_common_level q x x
    have hmt : q ^ m • ((t • x : qTors T G q) : G) = 0 := by
      rw [Submodule.coe_smul, smul_comm, hm, smul_zero]
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_smul' q l x hm, coe_smul' q l (t • x) hmt, Submodule.coe_smul, smul_comm]

scoped instance : SMulCommClass ℤ_[q] T (qTors T G q) := SMulCommClass.symm _ _ _

theorem natCast_smul_eq (k : ℕ) (x : qTors T G q) : ((k : ℤ_[q]) • x : qTors T G q) = k • x := by
  obtain ⟨m, -, hm, -⟩ := exists_common_level q x x
  apply Subtype.ext
  rw [coe_smul' q _ x hm, map_natCast, ZMod.val_natCast]
  rw [nsmul_eq_nsmul_of_modEq hm (Nat.mod_modEq k (q ^ m)), Submodule.coe_smul_of_tower]

open Pointwise

theorem H2card
    (A : Type*) [CommRing A] (G : Type*) [AddCommGroup G] [Module A G]
    (s : Set A) (hs : s.Finite) (hfin : Finite ↥(Submodule.torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(Submodule.torsionBySet A G s) :=
  CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet A G s hs hfin

scoped instance : SMulCommClass T ℤ_[q] (CharacterModule (qTors T G q)) where
  smul_comm t l φ := by
    apply DFunLike.ext; intro x
    simp only [CharacterModule.smul_apply]
    exact congrArg φ (smul_comm l t x)

scoped instance : SMulCommClass ℤ_[q] T (CharacterModule (qTors T G q)) := SMulCommClass.symm _ _ _

theorem pow_natCast_smul_eq (n : ℕ) (x : qTors T G q) : (((q : ℤ_[q]) ^ n) • x : qTors T G q) = q ^ n • x := by
  rw [← Nat.cast_pow, natCast_smul_eq]

theorem eq_zero_of_forall_exists_pow_smul (φ : CharacterModule (qTors T G q))
    (h : ∀ n : ℕ, ∃ ψ : CharacterModule (qTors T G q), ((q : ℤ_[q]) ^ n) • ψ = φ) : φ = 0 := by
  apply DFunLike.ext; intro x
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨ψ, rfl⟩ := h n
  rw [CharacterModule.smul_apply]
  have hx : (((q : ℤ_[q]) ^ n) • x : qTors T G q) = 0 := by
    apply Subtype.ext
    rw [pow_natCast_smul_eq, Submodule.coe_smul_of_tower, hn, Submodule.coe_zero]
  rw [hx, map_zero]
  rfl

omit hq in

theorem finite_pow_torsion (hfin : Finite ↥(torsionBy ℤ G (q : ℤ))) (n : ℕ) :
    Finite {x : G // q ^ n • x = 0} := by
  induction n with
  | zero =>
    haveI : Subsingleton {x : G // q ^ 0 • x = 0} := ⟨fun a b => Subtype.ext (by
      have ha : (1 : ℕ) • (a : G) = 0 := a.2
      have hb : (1 : ℕ) • (b : G) = 0 := b.2
      rw [one_nsmul] at ha hb
      rw [ha, hb])⟩
    infer_instance
  | succ n ih =>

    let A : AddSubgroup G :=
      { carrier := {x | q ^ (n + 1) • x = 0}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [nsmul_add, ha, hb, add_zero]
        neg_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [smul_neg, ha, neg_zero] }
    let f : A →+ G :=
      { toFun := fun a => q • (a : G)
        map_zero' := by simp
        map_add' := fun a b => by simp }
    haveI : Finite f.ker := by
      refine Finite.of_injective (fun a : f.ker => (⟨(a : A), ?_⟩ : torsionBy ℤ G (q : ℤ))) ?_
      · have := a.2; rw [AddMonoidHom.mem_ker] at this
        rw [mem_torsionBy_iff, natCast_zsmul]; exact this
      · intro a b h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
    haveI : Finite f.range := by
      haveI := ih
      refine Finite.of_injective (fun y : f.range => (⟨(y : G), ?_⟩ : {x : G // q ^ n • x = 0})) ?_
      · obtain ⟨a, ha⟩ := y.2
        rw [← ha]
        show q ^ n • (q • (a : G)) = 0
        rw [← mul_nsmul', ← pow_succ]; exact a.2
      · intro a b h
        have h' := congrArg Subtype.val h
        exact Subtype.ext h'
    have hcard : Nat.card A = Nat.card f.range * Nat.card f.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
    have hne : Nat.card A ≠ 0 := by
      rw [hcard]; exact mul_ne_zero (Nat.card_pos.ne') (Nat.card_pos.ne')
    have hA : Finite A := Nat.finite_of_card_ne_zero hne
    exact Finite.of_equiv A (Equiv.subtypeEquivRight (fun x => Iff.rfl))

theorem finite_quotient_q (hfin : Finite ↥(torsionBy ℤ G (q : ℤ))) :
    Finite (CharacterModule (qTors T G q) ⧸
      (Ideal.span {(q : ℤ_[q])} • (⊤ : Submodule ℤ_[q] (CharacterModule (qTors T G q))))) := by
  have hfin' : Finite ↥(torsionBySet ℤ_[q] (qTors T G q) {(q : ℤ_[q])}) := by
    refine Finite.of_injective (fun x => (⟨((x : qTors T G q) : G), ?_⟩ : torsionBy ℤ G (q : ℤ))) ?_
    · have hx := (mem_torsionBySet_iff _ _).1 x.2 ⟨(q : ℤ_[q]), rfl⟩
      have : ((q : ℤ_[q]) • (x : qTors T G q) : qTors T G q) = q • (x : qTors T G q) := natCast_smul_eq q q _
      rw [mem_torsionBy_iff, natCast_zsmul, ← Submodule.coe_smul_of_tower, ← this]
      exact congrArg (fun z : qTors T G q => (z : G)) hx
    · intro a b h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  have hc := H2card ℤ_[q] (qTors T G q) {(q : ℤ_[q])} (Set.finite_singleton _) hfin'
  have hne : Nat.card ↥(torsionBySet ℤ_[q] (qTors T G q) {(q : ℤ_[q])}) ≠ 0 := Nat.card_pos.ne'
  rw [← hc] at hne
  exact Nat.finite_of_card_ne_zero hne

theorem fg_top_of_separated {Y : Type*} [AddCommGroup Y] [Module ℤ_[q] Y]
    (hsep : ∀ y : Y, (∀ n : ℕ, ∃ z : Y, ((q : ℤ_[q]) ^ n) • z = y) → y = 0)
    [hF : Finite (Y ⧸ (Ideal.span {(q : ℤ_[q])} • (⊤ : Submodule ℤ_[q] Y)))] :
    (⊤ : Submodule ℤ_[q] Y).FG := by
  classical
  set N : Submodule ℤ_[q] Y := Ideal.span {(q : ℤ_[q])} • ⊤ with hN
  let sec : Y ⧸ N → Y := fun c => (Submodule.Quotient.mk_surjective N c).choose
  have hsec : ∀ c, Submodule.Quotient.mk (sec c) = c := fun c =>
    (Submodule.Quotient.mk_surjective N c).choose_spec
  obtain ⟨d, emb, hemb⟩ := (Set.finite_range sec).fin_embedding
  let v : Fin d → Y := fun i => emb i
  have hv : Set.range v = Set.range sec := hemb
  let W : Submodule ℤ_[q] Y := span ℤ_[q] (Set.range v)

  have hstep : ∀ y : Y, ∃ c : Fin d → ℤ_[q], ∃ y' : Y, y = (∑ i, c i • v i) + (q : ℤ_[q]) • y' := by
    intro y
    have h1 : y - sec (Submodule.Quotient.mk y) ∈ N := by
      rw [← Submodule.Quotient.eq, hsec]
    have h2 : sec (Submodule.Quotient.mk y) ∈ W :=
      Submodule.subset_span (by rw [hv]; exact ⟨_, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[q]).1 h2
    have h1' : y - sec (Submodule.Quotient.mk y) ∈ (q : ℤ_[q]) • (⊤ : Submodule ℤ_[q] Y) := by
      rw [← Submodule.ideal_span_singleton_smul]; exact h1
    obtain ⟨y', -, hy'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1'
    exact ⟨c, y', by rw [hc, hy']; abel⟩
  choose cf yf hcy using hstep

  have htop : ∀ y : Y, y ∈ W := by
    intro y
    let sq : ℕ → (Fin d → ℤ_[q]) × Y :=
      fun n => Nat.rec (0, y) (fun k p => (p.1 + ((q : ℤ_[q]) ^ k) • cf p.2, yf p.2)) n
    have sq_zero : sq 0 = (0, y) := rfl
    have sq_succ : ∀ k, sq (k + 1) = ((sq k).1 + ((q : ℤ_[q]) ^ k) • cf (sq k).2, yf (sq k).2) :=
      fun k => rfl
    have inv : ∀ n, y = (∑ i, (sq n).1 i • v i) + ((q : ℤ_[q]) ^ n) • (sq n).2 := by
      intro n
      induction n with
      | zero => simp [sq_zero]
      | succ k ih =>
        have h := hcy (sq k).2
        rw [sq_succ]
        calc y = (∑ i, (sq k).1 i • v i) + ((q : ℤ_[q]) ^ k) • (sq k).2 := ih
          _ = (∑ i, (sq k).1 i • v i)
                + ((q : ℤ_[q]) ^ k) • ((∑ i, cf (sq k).2 i • v i) + (q : ℤ_[q]) • yf (sq k).2) := by
              rw [← h]
          _ = (∑ i, ((sq k).1 + ((q : ℤ_[q]) ^ k) • cf (sq k).2) i • v i)
                + ((q : ℤ_[q]) ^ (k + 1)) • yf (sq k).2 := by
              rw [smul_add, smul_smul, ← pow_succ, ← add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_eq_mul, mul_smul]

    have hdiff : ∀ i k, (sq (k + 1)).1 i - (sq k).1 i ∈ Ideal.span {(q : ℤ_[q]) ^ k} := by
      intro i k
      rw [sq_succ]; dsimp only
      rw [Pi.add_apply, Pi.smul_apply, add_sub_cancel_left, smul_eq_mul]
      exact Ideal.mem_span_singleton'.2 ⟨cf (sq k).2 i, mul_comm _ _⟩
    have hcau : ∀ i n k, n ≤ k → (sq k).1 i - (sq n).1 i ∈ Ideal.span {(q : ℤ_[q]) ^ n} := by
      intro i n k hnk
      induction k with
      | zero =>
        obtain rfl : n = 0 := Nat.le_zero.1 hnk
        rw [sub_self]; exact zero_mem _
      | succ k ih =>
        rcases Nat.lt_or_ge k n with hlt | hge
        · obtain rfl : n = k + 1 := by omega
          rw [sub_self]; exact zero_mem _
        · have e : (sq (k + 1)).1 i - (sq n).1 i
              = ((sq (k + 1)).1 i - (sq k).1 i) + ((sq k).1 i - (sq n).1 i) := by abel
          rw [e]
          refine add_mem ?_ (ih hge)
          exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hge) (hdiff i k)

    have hI : ∀ n, (IsLocalRing.maximalIdeal ℤ_[q] ^ n • ⊤ : Submodule ℤ_[q] ℤ_[q])
        = (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := fun n => by
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]
    have hlim : ∀ i, ∃ L : ℤ_[q], ∀ n, (sq n).1 i - L ∈ Ideal.span {(q : ℤ_[q]) ^ n} := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal ℤ_[q]) (f := fun n => (sq n).1 i)
        (fun {m n} hmn => by
          rw [SModEq.sub_mem, hI]
          have := hcau i m n hmn
          rw [← neg_sub]; exact neg_mem this)
      exact ⟨L, fun n => by have := hL n; rw [SModEq.sub_mem, hI] at this; exact this⟩
    choose L hL using hlim

    have hw : (∑ i, L i • v i) ∈ W :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hyw : y - ∑ i, L i • v i = 0 := by
      apply hsep
      intro n

      have ha : ∀ i, ∃ a : ℤ_[q], a * (q : ℤ_[q]) ^ n = (sq n).1 i - L i :=
        fun i => Ideal.mem_span_singleton'.1 (hL i n)
      choose a ha using ha
      refine ⟨(sq n).2 + ∑ i, a i • v i, ?_⟩
      conv_rhs => rw [inv n]
      have key : ∀ i, (sq n).1 i • v i - L i • v i = ((q : ℤ_[q]) ^ n) • (a i • v i) := fun i => by
        rw [← sub_smul, ← ha i, smul_smul, mul_comm]
      rw [smul_add, Finset.smul_sum]
      simp only [← key]
      rw [Finset.sum_sub_distrib]
      abel
    rw [sub_eq_zero] at hyw
    rw [hyw]; exact hw
  have hW : W = ⊤ := eq_top_iff.2 fun y _ => htop y
  rw [← hW]
  exact Submodule.fg_span (Set.finite_range v)

theorem moduleFinite_X (hfin : Finite ↥(torsionBy ℤ G (q : ℤ))) :
    Module.Finite ℤ_[q] (CharacterModule (qTors T G q)) := by
  haveI := finite_quotient_q q (T := T) hfin
  exact ⟨fg_top_of_separated q (eq_zero_of_forall_exists_pow_smul q)⟩

theorem C1card
    (R : Type*) [CommRing R] [IsNoetherianRing R] (q : ℕ) [Fact q.Prime]
    (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
    (I : Ideal R) (hqI : (q : R) ∈ I)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) * q ^ C :=
  Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient R q hRq I hqI X

theorem finite_quotient_of_moduleFinite (R' : Type*) [CommRing R'] [Algebra ℤ_[q] R'] [Module.Finite ℤ_[q] R'] :
    Finite (R' ⧸ Ideal.span {(q : R')}) := by
  classical
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := ℤ_[q]) (M := R')
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  let F : (Fin k → ZMod q) → R' ⧸ Ideal.span {(q : R')} :=
    fun c => Ideal.Quotient.mk _ (∑ i, (((c i).val : ℕ) : ℤ_[q]) • v i)
  refine Finite.of_surjective F fun r => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hr : r ∈ span ℤ_[q] (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[q]).1 hr
  refine ⟨fun i => PadicInt.toZMod (l i), ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ r
  rw [Ideal.Quotient.eq, ← hl, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_smul]
  have hmem : ((((PadicInt.toZMod (l i)).val : ℕ) : ℤ_[q]) - l i) ∈ Ideal.span {(q : ℤ_[q])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [← hμ, mul_smul, Algebra.smul_def (q : ℤ_[q]), map_natCast, Algebra.smul_def μ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

omit hq in

theorem natCard_quotient_eq_of_mem_iff {A B : Type*} [Ring A] [Ring B] {M : Type*} [AddCommGroup M]
    [Module A M] [Module B M] (N : Submodule A M) (N' : Submodule B M) (h : ∀ x, x ∈ N ↔ x ∈ N') :
    Nat.card (M ⧸ N) = Nat.card (M ⧸ N') := by
  have h1 : Nat.card (M ⧸ N) = N.toAddSubgroup.index := by rw [AddSubgroup.index_eq_card]; rfl
  have h2 : Nat.card (M ⧸ N') = N'.toAddSubgroup.index := by rw [AddSubgroup.index_eq_card]; rfl
  have h3 : N.toAddSubgroup = N'.toAddSubgroup := by ext x; exact h x
  rw [h1, h2, h3]

section abstractY

variable (T)
variable (Y : Type*) [AddCommGroup Y] [Module ℤ_[q] Y] [Module T Y] [SMulCommClass T ℤ_[q] Y]

noncomputable def ρ : T →+* Module.End ℤ_[q] Y := Module.toModuleEnd ℤ_[q] (S := T) Y

theorem ρ_apply (t : T) (y : Y) : ρ (T := T) (q := q) (Y := Y) t y = t • y := rfl

noncomputable def Rsub : Subalgebra ℤ_[q] (Module.End ℤ_[q] Y) :=
  Algebra.adjoin ℤ_[q] (Set.range (ρ (T := T) (q := q) (Y := Y)))

theorem range_ρ_comm : ∀ a ∈ Set.range (ρ (T := T) (q := q) (Y := Y)), ∀ b ∈ Set.range (ρ (T := T) (q := q) (Y := Y)), a * b = b * a := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

scoped instance instIsMulCommutativeRsub : IsMulCommutative (Rsub (T := T) (q := q) (Y := Y)) :=
  Algebra.isMulCommutative_adjoin ℤ_[q] (range_ρ_comm (T := T) (q := q) (Y := Y))

theorem Rsub_smul_def (r : Rsub (T := T) (q := q) (Y := Y)) (y : Y) :
    r • y = (r : Module.End ℤ_[q] Y) y := rfl

scoped instance instIST1 : IsScalarTower ℤ_[q] (Rsub (T := T) (q := q) (Y := Y)) Y := ⟨fun _ _ _ => rfl⟩

scoped instance instIST2 : IsScalarTower (Rsub (T := T) (q := q) (Y := Y)) (Rsub (T := T) (q := q) (Y := Y)) Y :=
  ⟨fun a b y => by rw [smul_eq_mul, mul_smul]⟩

noncomputable def ρR : T →+* Rsub (T := T) (q := q) (Y := Y) :=
  (ρ (T := T) (q := q) (Y := Y)).codRestrict (Rsub (T := T) (q := q) (Y := Y)) fun t => Algebra.subset_adjoin ⟨t, rfl⟩

theorem ρR_smul (t : T) (y : Y) : (ρR (T := T) (q := q) (Y := Y) t) • y = t • y := rfl

theorem Rsub_apply_mem (J : Ideal T) (r : Module.End ℤ_[q] Y) (hr : r ∈ Rsub (T := T) (q := q) (Y := Y))
    (ψ : Y) (hψ : ψ ∈ J • (⊤ : Submodule T Y)) : r ψ ∈ J • (⊤ : Submodule T Y) := by
  refine Algebra.adjoin_induction
    (p := fun (r : Module.End ℤ_[q] Y) (_ : r ∈ Algebra.adjoin ℤ_[q] (Set.range (ρ (T := T) (q := q) (Y := Y)))) =>
      ∀ ψ : Y, ψ ∈ J • (⊤ : Submodule T Y) → r ψ ∈ J • (⊤ : Submodule T Y))
    ?_ ?_ ?_ ?_ hr ψ hψ
  · rintro _ ⟨t, rfl⟩ ψ hψ
    rw [ρ_apply]
    exact Submodule.smul_mem _ t hψ
  · intro l ψ hψ
    rw [Module.algebraMap_end_apply]
    refine Submodule.smul_induction_on hψ ?_ ?_
    · intro j hj χ _
      rw [← smul_comm j l χ]
      exact Submodule.smul_mem_smul hj Submodule.mem_top
    · intro a b ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a b _ _ ha hb ψ hψ
    rw [LinearMap.add_apply]
    exact Submodule.add_mem _ (ha ψ hψ) (hb ψ hψ)
  · intro a b _ _ ha hb ψ hψ
    rw [Module.End.mul_apply]
    exact ha _ (hb ψ hψ)

open scoped IsMulCommutative in

theorem mem_map_smul_top_iff (J : Ideal T) (φ : Y) :
    φ ∈ (J.map (ρR (T := T) (q := q) (Y := Y))) • (⊤ : Submodule (Rsub (T := T) (q := q) (Y := Y)) Y)
      ↔ φ ∈ J • (⊤ : Submodule T Y) := by
  constructor
  · intro hφ
    refine Submodule.smul_induction_on hφ ?_ ?_
    · intro r hr ψ _
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
      · rintro _ ⟨j, hj, rfl⟩
        show (ρR (T := T) (q := q) (Y := Y) j) • ψ ∈ _
        rw [ρR_smul]
        exact Submodule.smul_mem_smul hj Submodule.mem_top
      · show (0 : Rsub (T := T) (q := q) (Y := Y)) • ψ ∈ _
        rw [zero_smul]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        show (a + b) • ψ ∈ _
        rw [add_smul]; exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        show (a * b) • ψ ∈ _
        rw [mul_smul]
        exact Rsub_apply_mem (T := T) (q := q) (Y := Y) J (a : Module.End ℤ_[q] Y) a.2 _ hb
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · intro hφ
    refine Submodule.smul_induction_on hφ ?_ ?_
    · intro j hj ψ _
      show (ρR (T := T) (q := q) (Y := Y) j) • ψ ∈ _
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hj) Submodule.mem_top
    · intro a b ha hb; exact Submodule.add_mem _ ha hb

open scoped IsMulCommutative in

theorem Rsub_package [Module.Finite ℤ_[q] Y] :
    Module.Finite ℤ_[q] (Rsub (T := T) (q := q) (Y := Y)) ∧ IsNoetherianRing (Rsub (T := T) (q := q) (Y := Y)) ∧ Module.Finite (Rsub (T := T) (q := q) (Y := Y)) Y := by
  haveI : IsNoetherian ℤ_[q] (Module.End ℤ_[q] Y) := inferInstance
  haveI hRfin : Module.Finite ℤ_[q] (Rsub (T := T) (q := q) (Y := Y)) :=
    Module.Finite.of_injective (Rsub (T := T) (q := q) (Y := Y)).val.toLinearMap Subtype.val_injective
  haveI : IsNoetherianRing (Rsub (T := T) (q := q) (Y := Y)) :=
    isNoetherian_of_tower ℤ_[q] (inferInstance : IsNoetherian ℤ_[q] (Rsub (T := T) (q := q) (Y := Y)))
  haveI : Module.Finite (Rsub (T := T) (q := q) (Y := Y)) Y := Module.Finite.of_restrictScalars_finite ℤ_[q] (Rsub (T := T) (q := q) (Y := Y)) _
  exact ⟨hRfin, ‹_›, ‹_›⟩

noncomputable def smulTopΛ (J : Ideal T) : Submodule ℤ_[q] Y where
  carrier := ((J • ⊤ : Submodule T Y) : Set Y)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := by
    intro l φ hφ
    rw [SetLike.mem_coe] at hφ ⊢
    refine Submodule.smul_induction_on hφ ?_ ?_
    · intro j hj χ _
      rw [← smul_comm j l χ]
      exact Submodule.smul_mem_smul hj Submodule.mem_top
    · intro a b ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb

theorem mem_smulTopΛ (J : Ideal T) (φ : Y) :
    φ ∈ smulTopΛ (T := T) (q := q) (Y := Y) J ↔ φ ∈ J • (⊤ : Submodule T Y) := Iff.rfl

theorem exists_finset [Module.Finite ℤ_[q] Y] (J : Ideal T) (m : ℕ) (hqm : ((q : T) ^ m) ∈ J) :
    ∃ F : Finset T, (↑F : Set T) ⊆ J ∧ ((q : T) ^ m) ∈ F ∧
      (Ideal.span (↑F : Set T)) • (⊤ : Submodule T Y) = J • (⊤ : Submodule T Y) := by
  classical
  haveI : IsNoetherian ℤ_[q] Y := inferInstance
  obtain ⟨gens, hgens⟩ := IsNoetherian.noetherian (smulTopΛ (T := T) (q := q) (Y := Y) J)

  have hmem : ∀ g ∈ gens, ∃ Fg : Finset T, (↑Fg : Set T) ⊆ J ∧
      g ∈ (Ideal.span (↑Fg : Set T)) • (⊤ : Submodule T Y) := by
    intro g hg
    have hg' : g ∈ J • (⊤ : Submodule T Y) := by
      rw [← mem_smulTopΛ (T := T) (q := q) (Y := Y), ← hgens]; exact Submodule.subset_span hg
    rw [← Submodule.span_univ, ← Set.range_id, Submodule.mem_ideal_smul_span_iff_exists_sum] at hg'
    obtain ⟨a, ha, rfl⟩ := hg'
    refine ⟨a.support.image a, ?_, ?_⟩
    · intro t ht
      rw [Finset.coe_image] at ht
      obtain ⟨i, -, rfl⟩ := ht
      exact ha i
    · refine Submodule.sum_mem _ fun i hi => ?_
      exact Submodule.smul_mem_smul (Ideal.subset_span (Finset.mem_image_of_mem a hi)) Submodule.mem_top
  choose Fg hFg using hmem
  set F : Finset T := insert ((q : T) ^ m) (gens.attach.biUnion fun g => Fg g.1 g.2) with hFdef
  have hFJ : (↑F : Set T) ⊆ J := by
    intro t ht
    rw [hFdef, Finset.coe_insert, Set.mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact hqm
    · rw [Finset.mem_coe, Finset.mem_biUnion] at ht
      obtain ⟨g, -, htg⟩ := ht
      exact (hFg g.1 g.2).1 htg
  refine ⟨F, hFJ, Finset.mem_insert_self _ _, ?_⟩
  apply le_antisymm
  · exact Submodule.smul_mono_left (Ideal.span_le.2 hFJ)
  ·
    intro g hg
    have hg' : g ∈ smulTopΛ (T := T) (q := q) (Y := Y) J := hg
    rw [← hgens] at hg'
    have hle : Submodule.span ℤ_[q] (↑gens : Set Y) ≤ smulTopΛ (T := T) (q := q) (Y := Y) (Ideal.span (↑F : Set T)) := by
      rw [Submodule.span_le]
      intro g hg
      rw [SetLike.mem_coe, mem_smulTopΛ]
      refine Submodule.smul_mono_left ?_ (hFg g hg).2
      apply Ideal.span_mono
      intro t ht
      rw [hFdef, Finset.coe_insert]
      refine Set.mem_insert_of_mem _ ?_
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨⟨g, hg⟩, Finset.mem_attach _ _, ht⟩
    exact (mem_smulTopΛ (T := T) (q := q) (Y := Y) _ g).1 (hle hg')

open scoped IsMulCommutative in

theorem abstractHS [Module.Finite ℤ_[q] Y] (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (Y ⧸ (I ^ m • (⊤ : Submodule T Y))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (Y ⧸ (I ^ m • (⊤ : Submodule T Y))) * q ^ C := by
  obtain ⟨hfinR, hN, hF⟩ := Rsub_package (T := T) (q := q) (Y := Y)
  haveI := hfinR; haveI := hN; haveI := hF
  have hRq : Finite (Rsub (T := T) (q := q) (Y := Y) ⧸ Ideal.span {((q : ℕ) : Rsub (T := T) (q := q) (Y := Y))}) :=
    finite_quotient_of_moduleFinite q (Rsub (T := T) (q := q) (Y := Y))
  have hqI' : ((q : ℕ) : Rsub (T := T) (q := q) (Y := Y)) ∈ I.map (ρR (T := T) (q := q) (Y := Y)) := by
    have := Ideal.mem_map_of_mem (ρR (T := T) (q := q) (Y := Y)) hqI
    rwa [map_natCast] at this
  obtain ⟨e, C, hC⟩ := C1card (Rsub (T := T) (q := q) (Y := Y)) q hRq (I.map (ρR (T := T) (q := q) (Y := Y))) hqI' Y
  refine ⟨e, C, fun m => ?_⟩
  have hm := hC m
  rwa [← Ideal.map_pow, natCard_quotient_eq_of_mem_iff _ (I ^ m • (⊤ : Submodule T Y))
    (mem_map_smul_top_iff (T := T) (q := q) (Y := Y) (I ^ m))] at hm

end abstractY

section final

local notation "XM" => CharacterModule (qTors T G q)

theorem mem_qTors_of_mem_torsionBySet (I : Ideal T) (hqI : (q : T) ∈ I) (m : ℕ) (y : G)
    (hy : y ∈ torsionBySet T G (↑(I ^ m) : Set T)) : y ∈ qTors T G q := by
  refine ⟨m, ?_⟩
  have h' : ((q : T) ^ m) • y = 0 := (mem_torsionBySet_iff _ _).1 hy ⟨(q : T) ^ m, Ideal.pow_mem_pow hqI m⟩
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at h'

theorem smul_eq_zero_of_sep (F : Finset T) (I : Ideal T) (m : ℕ)
    (hFeq : (Ideal.span (↑F : Set T)) • (⊤ : Submodule T XM) = (I ^ m) • (⊤ : Submodule T XM))
    (x : qTors T G q) (hx : x ∈ torsionBySet T (qTors T G q) (↑F : Set T)) (u : T) (hu : u ∈ I ^ m) :
    u • x = 0 := by

  have key : ∀ ψ : XM, ψ ∈ (Ideal.span (↑F : Set T)) • (⊤ : Submodule T XM) → ψ x = 0 := by
    intro ψ hψ
    have hx' : x ∈ torsionBySet T (qTors T G q) ↑(Ideal.span (↑F : Set T)) := by
      rw [← torsionBySet_eq_torsionBySet_span]; exact hx
    refine Submodule.smul_induction_on hψ ?_ ?_
    · intro f hf χ _
      show χ (f • x) = 0
      rw [(mem_torsionBySet_iff _ _).1 hx' ⟨f, hf⟩, map_zero]
    · intro a b ha hb
      show a x + b x = 0
      rw [ha, hb, add_zero]
  by_contra hne
  obtain ⟨φ, hφ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  apply hφ
  have hmem : u • φ ∈ (Ideal.span (↑F : Set T)) • (⊤ : Submodule T XM) := by
    rw [hFeq]; exact Submodule.smul_mem_smul hu Submodule.mem_top
  exact key (u • φ) hmem

noncomputable def torsEquiv (F : Finset T) (I : Ideal T) (hqI : (q : T) ∈ I) (m : ℕ)
    (hFJ : (↑F : Set T) ⊆ ↑(I ^ m))
    (hFeq : (Ideal.span (↑F : Set T)) • (⊤ : Submodule T XM) = (I ^ m) • (⊤ : Submodule T XM)) :
    ↥(torsionBySet T (qTors T G q) (↑F : Set T)) ≃ ↥(torsionBySet T G (↑(I ^ m) : Set T)) where
  toFun x := ⟨((x : qTors T G q) : G), (mem_torsionBySet_iff _ _).2 fun u => by
      show (u : T) • ((x : qTors T G q) : G) = 0
      rw [← Submodule.coe_smul, smul_eq_zero_of_sep q F I m hFeq x x.2 u u.2, Submodule.coe_zero]⟩
  invFun y := ⟨⟨(y : G), mem_qTors_of_mem_torsionBySet q I hqI m (y : G) y.2⟩,
      (mem_torsionBySet_iff _ _).2 fun f => Subtype.ext (by
        rw [Submodule.coe_smul, Submodule.coe_zero]
        exact ((mem_torsionBySet_iff _ _).1 y.2 ⟨(f : T), hFJ f.2⟩ : (f : T) • (y : G) = 0))⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

theorem finite_torsionBySet_qTors (hfinq : Finite ↥(torsionBy ℤ G (q : ℤ))) (F : Finset T) (m : ℕ)
    (hqF : ((q : T) ^ m) ∈ F) : Finite ↥(torsionBySet T (qTors T G q) (↑F : Set T)) := by
  haveI := finite_pow_torsion q hfinq m
  refine Finite.of_injective
    (fun x => (⟨((x : qTors T G q) : G), ?_⟩ : {y : G // q ^ m • y = 0})) ?_
  · have h1 : ((q : T) ^ m) • (x : qTors T G q) = 0 := (mem_torsionBySet_iff _ _).1 x.2 ⟨(q : T) ^ m, hqF⟩
    have h2 : ((q : T) ^ m) • ((x : qTors T G q) : G) = 0 := by
      rw [← Submodule.coe_smul, h1, Submodule.coe_zero]
    rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at h2
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem card_eq (hfinq : Finite ↥(torsionBy ℤ G (q : ℤ))) (I : Ideal T) (hqI : (q : T) ∈ I) (m : ℕ) :
    Nat.card (XM ⧸ (I ^ m • (⊤ : Submodule T XM))) = Nat.card ↥(torsionBySet T G (↑(I ^ m) : Set T)) := by
  haveI : Module.Finite ℤ_[q] XM := moduleFinite_X q hfinq
  obtain ⟨F, hFJ, hqF, hFeq⟩ :=
    exists_finset (T := T) (q := q) (Y := XM) (I ^ m) m (Ideal.pow_mem_pow hqI m)
  have e1 : Nat.card (XM ⧸ (I ^ m • (⊤ : Submodule T XM)))
      = Nat.card (XM ⧸ ((Ideal.span (↑F : Set T)) • (⊤ : Submodule T XM))) := by rw [hFeq]
  haveI hfinF := finite_torsionBySet_qTors q hfinq F m hqF
  rw [e1, H2card T (qTors T G q) (↑F : Set T) F.finite_toSet hfinF]
  exact Nat.card_congr (torsEquiv q F I hqI m hFJ hFeq)

theorem brick (hfin : Finite ↥(torsionBy ℤ G (q : ℤ))) (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C := by
  haveI : Module.Finite ℤ_[q] XM := moduleFinite_X q hfin
  obtain ⟨e, C, hC⟩ := abstractHS (T := T) (q := q) (Y := XM) I hqI
  refine ⟨e, C, fun m => ?_⟩
  rw [← card_eq q hfin I hqI m]
  exact hC m

end final

end P2MBrick
p2m_reactivate "P2MW.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy.P2MBrick"

theorem solution
    (T : Type*) [CommRing T] (G : Type*) [AddCommGroup G] [Module T G]
    (q : ℕ) [Fact q.Prime] (hfin : Finite ↥(Submodule.torsionBy ℤ G (q : ℤ)))
    (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C :=
  P2MBrick.brick q hfin I hqI

end S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy
end P2MW
export P2MW.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy (solution)
