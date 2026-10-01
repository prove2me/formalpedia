-- Prove2me | solution 1 for ShorAlgorithms.Reduction.factor_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:33:35.572122+00:00
-- url     : https://prove2.me/submissions/ccf1438e-6400-4f00-9d1b-5ce17fe9783d

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_localOrder
import Definitions.Def_ShorAlgorithms_Reduction_successEvent
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace AShorCount
noncomputable section

open Classical in
theorem agree_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] (f : ∀ i, β i → ℕ)
    (hf : ∀ i e, 2 * Fintype.card {a : β i // f i a = e} ≤ Fintype.card (β i)) :
    2^(Fintype.card ι-1) * Fintype.card {u : ∀ i, β i // ∀ i j, f i (u i)=f j (u j)} ≤
      Fintype.card (∀ i, β i) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let J := {i : ι // i ≠ i₀}
  let S := {u : ∀ i, β i // ∀ i j, f i (u i)=f j (u j)}
  let T := Σ a : β i₀, ∀ i : J, {v : β i.1 // f i.1 v=f i₀ a}
  let enc : S → T := fun u => ⟨u.1 i₀,fun i => ⟨u.1 i.1,u.2 i.1 i₀⟩⟩
  let dec : T → ∀ i, β i := fun w => (Equiv.piSplitAt i₀ β).symm (w.1,fun i => (w.2 i).1)
  have hleft (u : S) : dec (enc u)=u.1 := by
    change (Equiv.piSplitAt i₀ β).symm ((Equiv.piSplitAt i₀ β) u.1)=u.1
    exact (Equiv.piSplitAt i₀ β).symm_apply_apply u.1
  have hinj : Function.Injective enc := by
    intro u v h
    apply Subtype.ext
    have hh := congrArg dec h
    simpa only [hleft] using hh
  have hc : Fintype.card S ≤ Fintype.card T := Fintype.card_le_of_injective enc hinj
  have hJ : Fintype.card J=Fintype.card ι-1 := by
    simp only [J,Fintype.card_subtype_compl,Fintype.card_subtype_eq]
  have hprod (a : β i₀) : 2^Fintype.card J *
      (∏ i : J, Fintype.card {v : β i.1 // f i.1 v=f i₀ a}) ≤
      ∏ i : J, Fintype.card (β i.1) := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun (i : J) _ => Nat.zero_le (2*Fintype.card {v : β i.1 // f i.1 v=f i₀ a}))
      (fun i _ => hf i.1 (f i₀ a))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using h
  have heq : Fintype.card (∀ i, β i) = Fintype.card (β i₀) * ∏ i : J, Fintype.card (β i.1) := by
    rw [Fintype.card_congr (Equiv.piSplitAt i₀ β),Fintype.card_prod,Fintype.card_pi]
  rw [heq]
  calc
    2^(Fintype.card ι-1) * Fintype.card S ≤ 2^(Fintype.card ι-1) * Fintype.card T := Nat.mul_le_mul_left _ hc
    _ = ∑ a : β i₀, 2^Fintype.card J * (∏ i : J, Fintype.card {v : β i.1 // f i.1 v=f i₀ a}) := by
      simp only [T,Fintype.card_sigma,Fintype.card_pi,Finset.mul_sum,hJ]
    _ ≤ ∑ _a : β i₀, ∏ i : J, Fintype.card (β i.1) := Finset.sum_le_sum (fun a _ => hprod a)
    _ = _ := by simp
end
end AShorCount

open ShorAlgorithms.Reduction
namespace AShor
noncomputable section

def localMap (n : ℕ) : (ZMod n)ˣ →* ∀ p : n.primeFactors, (ZMod (p.1 ^ n.factorization p.1))ˣ :=
  MonoidHom.pi fun p => Units.map
    (ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1))).toMonoidHom

theorem localMap_injective (n : ℕ) (hn : 0 < n) : Function.Injective (localMap n) := by
  intro u v huv
  apply Units.ext
  apply (ZMod.equivPi n hn.ne').injective
  funext p
  have hE (a : ZMod n) : ZMod.equivPi n hn.ne' a p =
      ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1)) a := by
    exact RingHom.congr_fun (Subsingleton.elim
      ((Pi.evalRingHom (fun p : n.primeFactors => ZMod (p.1 ^ n.factorization p.1)) p).comp
        (ZMod.equivPi n hn.ne').toRingHom)
      (ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1)))) a
  rw [hE,hE]
  exact congrArg (fun w : (ZMod (p.1 ^ n.factorization p.1))ˣ => (w : ZMod (p.1 ^ n.factorization p.1))) (congrFun huv p)

theorem order_local (n : ℕ) (hn : 0 < n) (u : (ZMod n)ˣ) :
    orderOf u = n.primeFactors.lcm (localOrder n u) := by
  rw [←orderOf_injective (localMap n) (localMap_injective n hn) u,Pi.orderOf]
  change Finset.univ.lcm (fun p : n.primeFactors => localOrder n u p.1) = n.primeFactors.lcm (localOrder n u)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro p hp
    exact Finset.dvd_lcm p.2
  · apply Finset.lcm_dvd
    intro p hp
    exact Finset.dvd_lcm (Finset.mem_univ (⟨p,hp⟩ : n.primeFactors))
end
end AShor

open Classical in
theorem AShor.agree_from_half (n : ℕ) (hodd : Odd n) (hn : 1 < n)
    (hhalf : ∀ p ∈ n.primeFactors, ∀ e, 2 * Nat.card {u : (ZMod (p^n.factorization p))ˣ //
      padicValNat 2 (orderOf u)=e} ≤ Nat.totient (p^n.factorization p)) :
    2^(n.primeFactors.card-1) * Nat.card {u : (ZMod n)ˣ //
      ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
        padicValNat 2 (localOrder n u p)=padicValNat 2 (localOrder n u q)} ≤ Nat.totient n := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let I := {p : ℕ // p ∈ n.primeFactors}
  haveI : Nonempty I := (Nat.nonempty_primeFactors.mpr hn).to_subtype
  haveI (p : I) : NeZero (p.1^n.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  let β := fun p : I => (ZMod (p.1^n.factorization p.1))ˣ
  let f := fun p : I => fun u : β p => padicValNat 2 (orderOf u)
  have hf (p : I) (e : ℕ) : 2*Fintype.card {a : β p // f p a=e} ≤ Fintype.card (β p) := by
    simpa only [β,f,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using hhalf p.1 p.2 e
  have hb := AShorCount.agree_bound β f hf
  let S := {u : (ZMod n)ˣ // ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
    padicValNat 2 (localOrder n u p)=padicValNat 2 (localOrder n u q)}
  let T := {u : ∀ p : I, β p // ∀ p q, f p (u p)=f q (u q)}
  let enc : S → T := fun u => ⟨localMap n u.1,fun p q => u.2 p.1 p.2 q.1 q.2⟩
  have hinj : Function.Injective enc := by
    intro u v h
    apply Subtype.ext
    apply localMap_injective n (by omega)
    exact congrArg Subtype.val h
  have hc : Fintype.card S ≤ Fintype.card T := Fintype.card_le_of_injective enc hinj
  have htotal : Fintype.card (∀ p : I, β p) = Nat.totient n := by
    let e := (Units.mapEquiv (ZMod.equivPi n (by omega)).toMulEquiv).trans MulEquiv.piUnits
    have h := Fintype.card_congr e.toEquiv
    rw [ZMod.card_units_eq_totient] at h
    exact h.symm
  have hI : Fintype.card I=n.primeFactors.card := Fintype.card_coe _
  simp only [← Nat.card_eq_fintype_card] at hb hc htotal hI
  rw [hI,htotal] at hb
  change 2^(n.primeFactors.card-1)*Nat.card S ≤ Nat.totient n
  exact (Nat.mul_le_mul_left _ hc).trans hb

open scoped BigOperators
namespace AShorCard
private theorem valuation_of_not_half {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r)
    (hhalf : ¬ d ∣ r/2) : padicValNat 2 d = padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hr
  have hk0 : k ≠ 0 := by intro h; simp [h] at hr
  have hk : ¬ 2 ∣ k := by
    rintro ⟨l,rfl⟩
    apply hhalf
    refine ⟨l,?_⟩
    rw [show d*(2*l)=(d*l)*2 by ring]
    omega
  rw [padicValNat.mul hd0 hk0,padicValNat.eq_zero_of_not_dvd hk,add_zero]


private theorem valuation_le_dvd {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

theorem cyclic_half (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (hN : Even (Fintype.card G)) (e : ℕ) :
    2 * Nat.card {u : G // padicValNat 2 (orderOf u) = e} ≤ Fintype.card G := by
  classical
  let N := Fintype.card G
  have hNp : 0 < N := Fintype.card_pos
  have hN2 : N/2*2=N := Nat.div_mul_cancel hN.two_dvd
  have hhpos : 0 < N/2 := by omega
  let K : Subgroup G := (powMonoidHom (N/2) : G →* G).ker
  have hKd : N/2 ∣ N := ⟨2,hN2.symm⟩
  have hKcard : Fintype.card K = N/2 := by
    have h := IsCyclic.card_powMonoidHom_ker G (N/2)
    simp only [Nat.card_eq_fintype_card] at h
    change Fintype.card K = N.gcd (N/2) at h
    rw [Nat.gcd_eq_right hKd] at h
    exact h
  have hKmem (u : G) : u ∈ K ↔ orderOf u ∣ N/2 := by
    change u^(N/2)=1 ↔ orderOf u ∣ N/2
    exact orderOf_dvd_iff_pow_eq_one.symm
  have hval : padicValNat 2 N = padicValNat 2 (N/2)+1 := by
    rw [←hN2,padicValNat.mul hhpos.ne' (by decide)]
    norm_num
  rw [Nat.card_eq_fintype_card]
  by_cases he : e = padicValNat 2 N
  · have hsub : (fun u : G => padicValNat 2 (orderOf u) = e) ≤ (fun u => u ∉ K) := by
      intro u hu hmem
      have hv := valuation_le_dvd hhpos.ne' ((hKmem u).mp hmem)
      rw [hu,he] at hv
      omega
    have hc := Fintype.card_subtype_mono _ _ hsub
    rw [Fintype.card_subtype_compl] at hc
    change Fintype.card {u : G // padicValNat 2 (orderOf u) = e} ≤ N - Fintype.card K at hc
    rw [hKcard] at hc
    omega
  · have hsub : (fun u : G => padicValNat 2 (orderOf u) = e) ≤ (fun u => u ∈ K) := by
      intro u hu
      rw [hKmem]
      by_contra hno
      have hv := valuation_of_not_half hNp.ne' (orderOf_dvd_card (x := u)) hno
      exact he (hu.symm.trans hv)
    have hc := Fintype.card_subtype_mono _ _ hsub
    change Fintype.card {u : G // padicValNat 2 (orderOf u) = e} ≤ Fintype.card K at hc
    rw [hKcard] at hc
    omega
end AShorCard

theorem shor_half (p α e : ℕ) (hp : p.Prime) (hodd : Odd p) (hα : 1 ≤ α) :
    2 * Nat.card {u : (ZMod (p ^ α))ˣ // padicValNat 2 (orderOf u) = e}
      ≤ Nat.totient (p ^ α) := by
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat dvd_rfl
  have hplt : 2 < p := by have := hp.two_le; omega
  have hpow : 2 < p^α := hplt.trans_le (by simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ p) hα)
  haveI : NeZero (p^α) := ⟨by omega⟩
  haveI : IsCyclic (ZMod (p^α))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 α
  have hc : Fintype.card (ZMod (p^α))ˣ = Nat.totient (p^α) := ZMod.card_units_eq_totient _
  have heven : Even (Fintype.card (ZMod (p^α))ˣ) := by rw [hc]; exact Nat.totient_even hpow
  simpa only [hc] using AShorCard.cyclic_half (ZMod (p^α))ˣ heven e
theorem shor_all_agree (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    2 ^ (n.primeFactors.card - 1) *
        Nat.card {u : (ZMod n)ˣ // ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
          padicValNat 2 (localOrder n u p) = padicValNat 2 (localOrder n u q)}
      ≤ Nat.totient n := by
  apply AShor.agree_from_half n hodd hn
  intro p hp e
  obtain ⟨hpp,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
  exact shor_half p (n.factorization p) e hpp (hodd.of_dvd_nat hpn)
    (hpp.factorization_pos_of_dvd hn0 hpn)

open ShorAlgorithms.Reduction

theorem shor_nontrivial_factor (n : ℕ) (hn : 1 < n) (u : (ZMod n)ˣ)
    (heven : Even (orderOf u)) (hne : (u : ZMod n) ^ (orderOf u / 2) ≠ -1) :
    1 < factorCandidate n u ∧ factorCandidate n u < n := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨hn⟩
  let v : ZMod n := (u : ZMod n) ^ (orderOf u / 2)
  have horder := orderOf_pos u
  have hdiv : orderOf u / 2 * 2 = orderOf u := Nat.div_mul_cancel heven.two_dvd
  have hhalf : orderOf u / 2 ≠ 0 := by omega
  have hv1 : v ≠ 1 := by
    intro hh
    have hu1 : u ^ (orderOf u / 2) = 1 := by
      apply Units.ext
      simpa [v] using hh
    exact pow_ne_one_of_lt_orderOf hhalf (Nat.div_lt_self horder (by norm_num)) hu1
  have hv0 : v ≠ 0 := by
    simpa only [v,Units.val_pow_eq_pow_val] using Units.ne_zero (u ^ (orderOf u / 2))
  have hvsq : v^2 = 1 := by
    dsimp [v]
    rw [←pow_mul,hdiv]
    exact congrArg (fun w : (ZMod n)ˣ => (w : ZMod n)) (pow_orderOf_eq_one u)
  have hval : 1 < v.val := by
    have hpos := ZMod.val_pos.mpr hv0
    have hneval : v.val ≠ 1 := by
      intro hh
      apply hv1
      have he := ZMod.natCast_zmod_val v
      rw [hh,Nat.cast_one] at he
      exact he.symm
    omega
  have hcast : ((v.val-1 : ℕ) : ZMod n) = v-1 := by
    rw [Nat.cast_sub (by omega),ZMod.natCast_zmod_val,Nat.cast_one]
  have hg1 : Nat.gcd (v.val-1) n ≠ 1 := by
    intro hh
    have hc : (v.val-1).Coprime n := hh
    have hu := (ZMod.isUnit_iff_coprime (v.val-1) n).mpr hc
    rw [hcast] at hu
    have hz : (v-1)*(v+1)=(v-1)*0 := by
      calc
        (v-1)*(v+1)=v^2-1 := by ring
        _ = 0 := by rw [hvsq,sub_self]
        _ = (v-1)*0 := by simp
    have hz' : v+1=0 := hu.mul_left_cancel hz
    exact hne (eq_neg_of_add_eq_zero_left hz')
  have hgp : 0 < Nat.gcd (v.val-1) n := Nat.gcd_pos_of_pos_right _ (by omega)
  refine ⟨by change 1 < Nat.gcd (v.val-1) n; omega,?_⟩
  change Nat.gcd (v.val-1) n < n
  exact (Nat.gcd_le_left n (by omega)).trans_lt ((Nat.sub_le _ _).trans_lt (ZMod.val_lt v))

private theorem valuation_of_not_half {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r)
    (hhalf : ¬ d ∣ r/2) : padicValNat 2 d = padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hr
  have hk0 : k ≠ 0 := by intro h; simp [h] at hr
  have hk : ¬ 2 ∣ k := by
    rintro ⟨l,rfl⟩
    apply hhalf
    refine ⟨l,?_⟩
    rw [show d*(2*l)=(d*l)*2 by ring]
    omega
  rw [padicValNat.mul hd0 hk0,padicValNat.eq_zero_of_not_dvd hk,add_zero]

private theorem local_divides (n : ℕ) (u : (ZMod n)ˣ) (p : ℕ) :
    localOrder n u p ∣ orderOf u :=
  orderOf_map_dvd (Units.map (ZMod.castHom (Nat.ordProj_dvd n p)
    (ZMod (p ^ n.factorization p))).toMonoidHom) u

theorem shor_fail_equal (n : ℕ) (hodd : Odd n) (hn : 1 < n) (u : (ZMod n)ˣ)
    (hfail : ¬ successEvent n u) :
    ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
      padicValNat 2 (localOrder n u p) = padicValNat 2 (localOrder n u q) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn2 : ¬ 2 ∣ n := by
    rintro ⟨k,hk⟩
    obtain ⟨j,hj⟩ := hodd
    omega
  by_cases heven : Even (orderOf u)
  · have hneg : (u : ZMod n) ^ (orderOf u / 2) = -1 := by
      by_contra hh
      have hg := shor_nontrivial_factor n hn u heven hh
      exact hfail ⟨heven,hg⟩
    have hval (p : ℕ) (hp : p ∈ n.primeFactors) :
        padicValNat 2 (localOrder n u p) = padicValNat 2 (orderOf u) := by
      obtain ⟨hpp,hpn,hpn0⟩ := Nat.mem_primeFactors.mp hp
      have hpne : p ≠ 2 := by intro hh; subst p; exact hn2 hpn
      have hpgt : 2 < p := by have := hpp.two_le; omega
      have ha := hpp.factorization_pos_of_dvd hpn0 hpn
      have hpow : p ≤ p ^ n.factorization p := by
        simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ p) ha
      haveI : Fact (2 < p ^ n.factorization p) := ⟨hpgt.trans_le hpow⟩
      have hpneg : ((localUnit n u p : (ZMod (p ^ n.factorization p))ˣ) : ZMod (p ^ n.factorization p)) ^
          (orderOf u / 2) = -1 := by
        have hh := congrArg (ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p))) hneg
        change (ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)) (u : ZMod n)) ^ (orderOf u / 2) = -1
        simpa only [map_pow,map_neg,map_one] using hh
      apply valuation_of_not_half (orderOf_pos u).ne' (local_divides n u p)
      intro hd
      have hh : localUnit n u p ^ (orderOf u / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
      have hh' := congrArg (fun w : (ZMod (p ^ n.factorization p))ˣ => (w : ZMod (p ^ n.factorization p))) hh
      simp only [Units.val_pow_eq_pow_val,Units.val_one] at hh'
      rw [hpneg] at hh'
      exact ZMod.neg_one_ne_one hh'
    intro p hp q hq
    exact (hval p hp).trans (hval q hq).symm
  · have hnorder : ¬ 2 ∣ orderOf u := by
      intro h
      exact heven (even_iff_two_dvd.mpr h)
    have hv (p : ℕ) : padicValNat 2 (localOrder n u p) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hnorder (h.trans (local_divides n u p)))
    intro p hp q hq
    rw [hv,hv]
open ShorAlgorithms.Reduction

open Classical in
theorem AShor.prob_from_counts (n : ℕ) (hn : 1 < n)
    (hfail : ∀ u : (ZMod n)ˣ, ¬ successEvent n u →
      ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
        padicValNat 2 (localOrder n u p)=padicValNat 2 (localOrder n u q))
    (hcount : 2^(n.primeFactors.card-1)*Nat.card {u : (ZMod n)ˣ //
      ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
        padicValNat 2 (localOrder n u p)=padicValNat 2 (localOrder n u q)} ≤ Nat.totient n) :
    (1-1/2^(n.primeFactors.card-1) : ℝ)*(Nat.totient n : ℝ) ≤
      (Nat.card {u : (ZMod n)ˣ // successEvent n u} : ℝ) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let S := {u : (ZMod n)ˣ // successEvent n u}
  let F := {u : (ZMod n)ˣ // ¬ successEvent n u}
  let B := {u : (ZMod n)ˣ // ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
    padicValNat 2 (localOrder n u p)=padicValNat 2 (localOrder n u q)}
  have hFB : Fintype.card F ≤ Fintype.card B := Fintype.card_subtype_mono _ _ hfail
  have hsum : Fintype.card S + Fintype.card F = Nat.totient n := by
    have h := Fintype.card_subtype_compl (successEvent n)
    have hle := Fintype.card_subtype_le (successEvent n)
    change Fintype.card F = Fintype.card (ZMod n)ˣ - Fintype.card S at h
    change Fintype.card S ≤ Fintype.card (ZMod n)ˣ at hle
    rw [ZMod.card_units_eq_totient] at h hle
    omega
  have hmul : 2^(n.primeFactors.card-1)*Fintype.card F ≤ Nat.totient n := by
    apply (Nat.mul_le_mul_left _ hFB).trans
    simpa only [Nat.card_eq_fintype_card] using hcount
  have hr : (2:ℝ)^(n.primeFactors.card-1)*(Fintype.card F : ℝ) ≤ (Nat.totient n : ℝ) := by exact_mod_cast hmul
  have hsr : (Fintype.card S : ℝ)+(Fintype.card F : ℝ)=(Nat.totient n : ℝ) := by exact_mod_cast hsum
  have hf : (Fintype.card F : ℝ) ≤ (Nat.totient n : ℝ)/(2:ℝ)^(n.primeFactors.card-1) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hr)
  rw [Nat.card_eq_fintype_card]
  change (1-1/2^(n.primeFactors.card-1) : ℝ)*(Nat.totient n : ℝ) ≤ (Fintype.card S : ℝ)
  rw [sub_mul,one_mul,one_div,inv_mul_eq_div]
  linarith
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    (1 - 1 / 2 ^ (n.primeFactors.card - 1) : ℝ) * (Nat.totient n : ℝ)
      ≤ (Nat.card {u : (ZMod n)ˣ // successEvent n u} : ℝ) := by
  exact AShor.prob_from_counts n hn (fun u hfail => shor_fail_equal n hodd hn u hfail)
    (shor_all_agree n hodd hn)
