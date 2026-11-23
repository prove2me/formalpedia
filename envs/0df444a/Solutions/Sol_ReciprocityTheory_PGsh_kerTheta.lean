-- Prove2me | solution 1 for ReciprocityTheory.PGsh.kerTheta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:10.238568+00:00
-- url     : https://prove2.me/submissions/c50e269d-6244-4d9e-b8e1-bb27c5f1f011

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DvdOfCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
private theorem mem_span_of_step {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    x ∈ span {a} := by
  choose Y X hYX using h
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → {z // P z}, g 0 = ⟨x, hx⟩ ∧
      ∀ n, g (n + 1) = ⟨X (g n).1 (g n).2, (hYX (g n).1 (g n).2).2⟩ :=
    ⟨fun n => Nat.rec (motive := fun _ => {z // P z}) ⟨x, hx⟩
      (fun _ z => ⟨X z.1 z.2, (hYX z.1 z.2).2⟩) n, rfl, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → A, ∀ n, (g n).1 = a * y n + q * (g (n + 1)).1 :=
    ⟨fun n => Y (g n).1 (g n).2, fun n => by rw [hgs n]; exact (hYX _ _).1⟩
  have hmem : ∀ (n : ℕ) (z : A), z ∈ ((span {q}) ^ n • ⊤ : Submodule A A) ↔ q ^ n ∣ z := by
    intro n z
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have key : ∀ n, x = a * (∑ i ∈ Finset.range n, q ^ i * y i) + q ^ n * (g n).1 := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [hy n] at ih
      linear_combination ih
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      (∑ i ∈ Finset.range m, q ^ i * y i) ≡ (∑ i ∈ Finset.range n, q ^ i * y i)
        [SMOD ((span {q}) ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hmem]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [Finset.sum_range_add, show ∀ u w : A, u - (u + w) = -w from fun u w => by ring, dvd_neg]
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (pow_dvd_pow q (Nat.le_add_right m j)) _
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {q}) inferInstance
    (f := fun n => ∑ i ∈ Finset.range n, q ^ i * y i) hcau
  have hz : x - a * L = 0 := by
    refine IsHausdorff.haus (I := span {q}) inferInstance _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hmem]
    have hd : q ^ n ∣ (∑ i ∈ Finset.range n, q ^ i * y i) - L :=
      (hmem n _).1 (SModEq.sub_mem.1 (hL n))
    have e : x - a * L = a * ((∑ i ∈ Finset.range n, q ^ i * y i) - L) + q ^ n * (g n).1 := by
      linear_combination key n
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hd a) (dvd_mul_right _ _)
  exact Ideal.mem_span_singleton'.2 ⟨L, by linear_combination -hz⟩
variable {p : ℕ} [hp : Fact p.Prime]
section Sharp
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
private theorem sh_pow_succ (x : PreTilt O p) (n : ℕ) : sh x (n + 1) ^ p = sh x n := by
  unfold sh
  rw [Function.iterate_succ_apply', ← map_pow]
  congr 1
  have h := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x)
  rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h
private theorem sh_pow (x : PreTilt O p) (n : ℕ) : sh x n ^ p ^ n = x.untilt := by
  induction n with
  | zero => simp [sh]
  | succ n ih => rw [pow_succ', pow_mul, sh_pow_succ, ih]
private theorem preTilt_coeff_succ_pow_p (f : PreTilt O p) (n : ℕ) :
    PreTilt.coeff (n + 1) (f ^ p) = PreTilt.coeff n f := by
  exact Perfection.coeff_pow_p f n
private theorem preTilt_ext_coeff {x y : PreTilt O p} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) :
    x = y := by
  exact Perfection.ext h
private theorem preTilt_coeff_iterate_frobenius_symm (y : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] y) =
      PreTilt.coeff (m + n) y := by
  induction n generalizing y m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    conv_rhs => rw [← (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply y]
    rw [_root_.frobeniusEquiv_apply, frobenius_def, ← Nat.add_assoc]
    exact (preTilt_coeff_succ_pow_p _ _).symm
private theorem witt_exists_eq_teichmuller_coeff_zero_add_p_mul {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (x : WittVector p R) :
    ∃ z, x = teichmuller p (x.coeff 0) + (p : WittVector p R) * z := by
  obtain ⟨w, hw⟩ : ∃ w, w = x - teichmuller p (x.coeff 0) := ⟨_, rfl⟩
  have hx : x = teichmuller p (x.coeff 0) + w := by rw [hw]; ring
  have hw0 : w.coeff 0 = 0 := by
    have h := congrArg (fun y : WittVector p R => y.coeff 0) hx
    simp only [WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero] at h
    linear_combination -h
  by_cases hw' : w = 0
  · refine ⟨0, ?_⟩
    have h1 := hx
    rw [hw', add_zero] at h1
    rw [mul_zero, add_zero]
    exact h1
  · obtain ⟨m, b, hb, hwb⟩ := WittVector.exists_eq_pow_p_mul w hw'
    cases m with
    | zero =>
      rw [pow_zero, one_mul] at hwb
      rw [hwb] at hw0
      exact absurd hw0 hb
    | succ m =>
      refine ⟨(p : WittVector p R) ^ m * b, ?_⟩
      conv_lhs => rw [hx, hwb]
      ring
private theorem mk_sh (x : PreTilt O p) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (sh x n) = PreTilt.coeff n x := by
  unfold sh
  rw [PreTilt.mk_untilt_eq_coeff_zero, preTilt_coeff_iterate_frobenius_symm, Nat.zero_add]
end Sharp
section Ker
variable (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal)
  {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
include hv
private theorem p_ne_zero : (p : O) ≠ 0 := by
  intro h
  have h2 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
  rw [map_natCast] at h2
  exact (Nat.cast_ne_zero.2 hp.out.ne_zero) h2
private theorem torsionFree {a : O} (h : (p : O) * a = 0) : a = 0 := by
  apply hv.hom_inj
  have h2 := congrArg (algebraMap O C) h
  rw [map_mul, map_natCast, map_zero] at h2
  rw [map_zero]
  exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hp.out.ne_zero)
private theorem isDomain_integers : IsDomain O := by
  have : Nontrivial O := ⟨⟨1, 0, fun h => one_ne_zero ((map_one (algebraMap O C)).symm.trans
    ((congrArg (algebraMap O C) h).trans (map_zero _)))⟩⟩
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj
private theorem dvd_of_coeff_zero (pflat : PreTilt O p) (hpf : pflat.untilt = (p : O))
    (c : PreTilt O p) (hc : PreTilt.coeff 0 c = 0) : ∃ d, c = pflat * d := by
  have := isDomain_integers C v hv
  have hpn : (p : O) ≠ 0 := p_ne_zero C v hv
  have hpi : ∀ n, sh pflat n ≠ 0 := by
    intro n h0
    have h1 := sh_pow pflat n
    rw [h0, zero_pow (pow_ne_zero n hp.out.ne_zero), hpf] at h1
    exact hpn h1.symm
  obtain ⟨u, hu⟩ : (p : O) ∣ c.untilt := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (mk_sh c 0).trans hc
  have hdvd : ∀ n, sh pflat n ∣ sh c n := by
    intro n
    apply hv.dvd_of_le
    have h1 : v (algebraMap O C (sh c n)) ^ (p ^ n) ≤
        v (algebraMap O C (sh pflat n)) ^ (p ^ n) := by
      rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sh_pow, sh_pow, hpf, hu, map_mul, map_mul]
      exact mul_le_of_le_one_right zero_le (hv.map_le_one u)
    have hn : p ^ n ≠ 0 := pow_ne_zero n hp.out.ne_zero
    exact (pow_le_pow_iff_left₀ zero_le zero_le hn).1 h1
  choose D hD using hdvd
  have hDp : ∀ n, D (n + 1) ^ p = D n := by
    intro n
    have h1 := sh_pow_succ c n
    rw [hD (n + 1), hD n, mul_pow, sh_pow_succ] at h1
    exact mul_left_cancel₀ (hpi n) h1
  let d : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (D n),
    fun n => by rw [← map_pow, hDp]⟩
  refine ⟨d, preTilt_ext_coeff fun n => ?_⟩
  have hdn : PreTilt.coeff n d = Ideal.Quotient.mk (span {(p : O)}) (D n) := by
    rfl
  rw [map_mul, hdn, ← mk_sh c n, ← mk_sh pflat n, hD n, map_mul]
private theorem preTilt_eq_zero_of_untilt_eq_zero (x : PreTilt O p) (h : x.untilt = 0) : x = 0 := by
  have hs : ∀ n, sh x n = 0 := by
    intro n
    apply hv.hom_inj
    rw [map_zero]
    have h2 := congrArg (algebraMap O C) (sh_pow x n)
    rw [h, map_zero, map_pow] at h2
    first
    | exact pow_eq_zero h2
    | exact pow_eq_zero_iff (pow_ne_zero n hp.out.ne_zero) |>.1 h2
  apply preTilt_ext_coeff
  intro n
  rw [map_zero, ← mk_sh x n, hs n, map_zero]
end Ker
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
variable (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal)
  {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
include hv
namespace ReciprocityTheory.PGsh
theorem _root_.solution : KerThetaStatement p O := by
  have := isDomain_integers C v hv
  intro pflat hpf
  have hpn : (p : O) ≠ 0 := p_ne_zero C v hv
  have hθt : ∀ y : PreTilt O p, fontaineTheta O p (teichmuller p y) = y.untilt :=
    fun y => fontaineTheta_teichmuller y
  have hmkp : Ideal.Quotient.mk (span {(p : O)}) (p : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hξ : fontaineTheta O p ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) = 0 := by
    rw [map_sub, map_natCast, hθt, hpf, sub_self]
  have hmod : ∀ x : WittVector p (PreTilt O p),
      Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta O p x) = PreTilt.coeff 0 (x.coeff 0) := by
    intro x
    obtain ⟨z, hz⟩ := witt_exists_eq_teichmuller_coeff_zero_add_p_mul x
    conv_lhs => rw [hz]
    rw [map_add, map_mul, map_natCast, hθt, map_add, map_mul, hmkp, zero_mul, add_zero]
    exact mk_sh (x.coeff 0) 0
  have hfac : ∀ x : WittVector p (PreTilt O p),
      Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta O p x) = 0 →
      ∃ d z, x = teichmuller p pflat * teichmuller p d + (p : WittVector p (PreTilt O p)) * z := by
    intro x hx
    obtain ⟨z, hz⟩ := witt_exists_eq_teichmuller_coeff_zero_add_p_mul x
    rw [hmod] at hx
    obtain ⟨d, hd⟩ := dvd_of_coeff_zero C v hv pflat hpf _ hx
    exact ⟨d, z, by rw [hz, hd, map_mul]⟩
  refine ⟨le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hξ)),
    ?_, ?_⟩
  · refine mem_span_of_step (p : WittVector p (PreTilt O p)) _
      (fun x => fontaineTheta O p x = 0) ?_ x (RingHom.mem_ker.1 hx)
    intro x (hx0 : fontaineTheta O p x = 0)
    obtain ⟨d, z, hdz⟩ := hfac x (by rw [hx0, map_zero])
    refine ⟨-teichmuller p d, teichmuller p d + z, ?_, ?_⟩
    · rw [hdz]; ring
    · show fontaineTheta O p (teichmuller p d + z) = 0
      apply torsionFree (p := p) C v hv
      have e : (p : WittVector p (PreTilt O p)) * (teichmuller p d + z) =
          x + ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) * teichmuller p d := by
        rw [hdz]; ring
      rw [← map_natCast (fontaineTheta O p) p, ← map_mul, e, map_add, map_mul, hx0, hξ, zero_mul,
        add_zero]
  · have hu0 : PreTilt.untilt (0 : PreTilt O p) = 0 := by
      have e := map_mul PreTilt.untilt (0 : PreTilt O p) pflat
      rw [zero_mul, hpf] at e
      have e2 : PreTilt.untilt (0 : PreTilt O p) * (1 - (p : O)) = 0 := by linear_combination e
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact ((Fact.out : ¬IsUnit (p : O)) (by rw [← sub_eq_zero.1 h]; exact isUnit_one)).elim
    have hnz : ∀ a b : PreTilt O p, a * b = 0 → a = 0 ∨ b = 0 := by
      intro a b hab
      have h1 : a.untilt * b.untilt = 0 := by rw [← map_mul, hab, hu0]
      rcases mul_eq_zero.1 h1 with h | h
      · exact Or.inl (preTilt_eq_zero_of_untilt_eq_zero C v hv a h)
      · exact Or.inr (preTilt_eq_zero_of_untilt_eq_zero C v hv b h)
    have : NoZeroDivisors (PreTilt O p) := ⟨fun {a b} h => hnz a b h⟩
    have hπ : pflat ≠ 0 := fun h => hpn (by rw [← hpf, h, hu0])
    have hne : ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : WittVector p (PreTilt O p) => w.coeff 0) (sub_eq_zero.1 h)
      simp only [WittVector.teichmuller_coeff_zero, WittVector.coeff_p_zero] at h2
      exact hπ h2.symm
    exact mem_nonZeroDivisors_of_ne_zero hne
  · apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply] at hx
      obtain ⟨d, z, hdz⟩ := hfac x hx
      exact Ideal.mem_span_pair.2 ⟨z, teichmuller p d, by rw [hdz]; ring⟩
    · rw [Ideal.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, map_natCast, hmkp]
      · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, hθt, hpf, hmkp]
end ReciprocityTheory.PGsh
