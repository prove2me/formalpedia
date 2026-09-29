-- Prove2me | solution 1 for OddPerfectNumber.three_geom_sum_prime_power_index_prime_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T03:27:28.099464+00:00
-- url     : https://prove2.me/submissions/f67b3eeb-dd33-4852-95ff-835c422c0d7e

import Mathlib

/-!
Target: `OddPerfectNumber.three_geom_sum_prime_power_index_prime_v2`.

If `1 < b`, `1 < t`, `t` odd, `r` prime, `0 < beta` and `∑_{i<t} b^i = r^beta`,
then `t` is prime.

Elementary proof (no lifting-the-exponent lemma is used):

* `p2mX_powEq`      : `(c+1)^n = 1 + c * ∑_{i<n} (c+1)^i`.
* `p2mX_splitSum`   : `∑_{i<u*v} x^i = (∑_{i<u} x^i) * (∑_{j<v} (x^u)^j)`.
* `p2mX_geomExpand` : `∑_{j<n} (r*K+1)^j = n + r*K*(∑_{j<n} j) + r*r*Z`
                 (the "mod `r^2`" expansion, one induction).

`key`: for every splitting `t = u*v` with `1 < u`, `1 < v`, both factors of
`∑_{i<t} b^i = (∑_{i<u} b^i) * (∑_{j<v} (b^u)^j) = r^beta` exceed `1`, hence both
are divisible by `r`.  From `r ∣ ∑_{i<u} b^i` we get `b^u = r*K+1`, so the second
factor is `≡ v (mod r)`; as `r` divides it, `r ∣ v`.

Main argument by contradiction (`t` not prime):
1. Pick a prime `q ∣ t`; then `t = u*q` with `1 < u`, so `key` gives `r ∣ q`,
   i.e. `r = q`.  Hence `r ∣ t` and `r < t`.
2. Write `t = r*w` with `1 < w`.  `key r w` gives `r ∣ ∑_{i<r} b^i`, so
   `b^r ≡ 1 (mod r)`; Fermat (`ZMod.pow_card`) gives `b ≡ 1 (mod r)`, i.e.
   `r ∣ c` where `b = c+1`.
3. `r ∣ t` with `t` odd forces `r` odd, say `r = 2*s+1`; then `∑_{j<r} j = r*s`.
4. Put `C = b^w = r*K+1`.  By `p2mX_geomExpand`, `D = ∑_{j<r} C^j = r + r*r*W`.
   Also `D ∣ r^beta` and `1 < D`, so `D = r^γ`; `r*r ∤ D` forces `γ = 1`, i.e.
   `D = r`.  But `D > r` since `C ≥ 2` and `r ≥ 2`.  Contradiction.
-/

private lemma p2mX_powEq (c n : ℕ) :
    (c + 1) ^ n = 1 + c * ∑ i ∈ Finset.range n, (c + 1) ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, ih]
    ring

private lemma p2mX_splitSum (x u v : ℕ) :
    ∑ i ∈ Finset.range (u * v), x ^ i
      = (∑ i ∈ Finset.range u, x ^ i) * ∑ j ∈ Finset.range v, (x ^ u) ^ j := by
  induction v with
  | zero => simp
  | succ v ih =>
    have h : u * (v + 1) = u * v + u := by ring
    rw [h, Finset.sum_range_add, ih, Finset.sum_range_succ, ← pow_mul]
    simp only [pow_add]
    rw [← Finset.mul_sum]
    ring

private lemma p2mX_geomExpand (r K n : ℕ) :
    ∃ Z, (∑ j ∈ Finset.range n, (r * K + 1) ^ j)
      = n + r * K * (∑ j ∈ Finset.range n, j) + r * r * Z := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨Z, hZ⟩ := ih
    refine ⟨Z + K * K * (∑ j ∈ Finset.range n, j) + r * K * Z, ?_⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ, p2mX_powEq (r * K) n, hZ]
    ring

private lemma p2mX_le_geom (x n : ℕ) (hx : 0 < x) : n ≤ ∑ i ∈ Finset.range n, x ^ i := by
  have h : ∑ _i ∈ Finset.range n, 1 ≤ ∑ i ∈ Finset.range n, x ^ i :=
    Finset.sum_le_sum (fun i _ => Nat.one_le_pow i x hx)
  simpa using h

private lemma p2mX_lt_geom (x n : ℕ) (hx : 1 < x) (hn : 1 < n) :
    n < ∑ i ∈ Finset.range n, x ^ i := by
  have h1 : (1 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have h : ∑ _i ∈ Finset.range n, 1 < ∑ i ∈ Finset.range n, x ^ i :=
    Finset.sum_lt_sum (fun i _ => Nat.one_le_pow i x (by omega))
      ⟨1, h1, by simpa using hx⟩
  simpa using h

theorem solution (b t r beta : Nat) (hb : 1 < b) (ht : 1 < t) (hodd : Odd t)
    (hr : r.Prime) (hβ : 0 < beta)
    (hgeom : (Finset.range t).sum (fun i => b ^ i) = r ^ beta) : t.Prime := by
  classical
  by_contra hnp
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hc : 0 < c := by omega
  have hr2 : 2 ≤ r := hr.two_le
  have hgeom' : ∑ i ∈ Finset.range t, (c + 1) ^ i = r ^ beta := hgeom
  -- divisors of `r ^ beta` that exceed `1` are multiples of `r`
  have hrdvd : ∀ X Y : ℕ, X * Y = r ^ beta → 1 < X → r ∣ X := by
    intro X Y hXY hX1
    obtain ⟨i, _, hXi⟩ := (Nat.dvd_prime_pow hr).mp ⟨Y, hXY.symm⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero] at hXi; omega
    · rw [hXi]; exact dvd_pow_self r (by omega)
  -- KEY STEP
  have key : ∀ u v : ℕ, 1 < u → 1 < v → t = u * v →
      r ∣ (∑ i ∈ Finset.range u, (c + 1) ^ i) ∧ r ∣ v := by
    intro u v hu hv htuv
    have hAB : (∑ i ∈ Finset.range u, (c + 1) ^ i) *
        (∑ j ∈ Finset.range v, ((c + 1) ^ u) ^ j) = r ^ beta := by
      rw [← p2mX_splitSum (c + 1) u v, show u * v = t from htuv.symm]
      exact hgeom'
    have hA1 : 1 < ∑ i ∈ Finset.range u, (c + 1) ^ i :=
      lt_of_lt_of_le hu (p2mX_le_geom (c + 1) u (by omega))
    have hB1 : 1 < ∑ j ∈ Finset.range v, ((c + 1) ^ u) ^ j :=
      lt_of_lt_of_le hv (p2mX_le_geom ((c + 1) ^ u) v (Nat.one_le_pow u (c + 1) (by omega)))
    have hrA : r ∣ ∑ i ∈ Finset.range u, (c + 1) ^ i := hrdvd _ _ hAB hA1
    have hBA : (∑ j ∈ Finset.range v, ((c + 1) ^ u) ^ j) *
        (∑ i ∈ Finset.range u, (c + 1) ^ i) = r ^ beta := by
      rw [mul_comm]; exact hAB
    have hrB : r ∣ ∑ j ∈ Finset.range v, ((c + 1) ^ u) ^ j := hrdvd _ _ hBA hB1
    refine ⟨hrA, ?_⟩
    obtain ⟨a1, ha1⟩ := hrA
    have hpu : (c + 1) ^ u = r * (c * a1) + 1 := by
      rw [p2mX_powEq c u, ha1]; ring
    obtain ⟨z, hz⟩ := p2mX_geomExpand r (c * a1) v
    have hBz : (∑ j ∈ Finset.range v, ((c + 1) ^ u) ^ j)
        = v + (r * (c * a1) * (∑ j ∈ Finset.range v, j) + r * r * z) := by
      rw [hpu, hz]; ring
    rw [hBz] at hrB
    have hd1 : r ∣ r * (c * a1) * (∑ j ∈ Finset.range v, j) + r * r * z :=
      ⟨(c * a1) * (∑ j ∈ Finset.range v, j) + r * z, by ring⟩
    have hsub := Nat.dvd_sub hrB hd1
    simpa using hsub
  -- Step 1 : every prime factor of `t` equals `r`; in particular `r ∣ t`, `r < t`
  obtain ⟨q, hqp, hqd⟩ : ∃ q, q.Prime ∧ q ∣ t := Nat.exists_prime_and_dvd (by omega)
  obtain ⟨u, hu⟩ := hqd
  have hq1 : 1 < q := hqp.one_lt
  have hu1 : 1 < u := by
    rcases Nat.lt_or_ge 1 u with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos u with h0 | hp
      · rw [h0, mul_zero] at hu; omega
      · have hu' : u = 1 := by omega
        rw [hu', mul_one] at hu
        exact hnp (by rw [hu]; exact hqp)
  have hrq : r ∣ q := (key u q hu1 hq1 (by rw [hu]; ring)).2
  have hreq : r = q := (Nat.prime_dvd_prime_iff_eq hr hqp).mp hrq
  have hrt : r ∣ t := by rw [hreq, hu]; exact ⟨u, rfl⟩
  have hrlt : r < t := by
    rcases Nat.lt_or_ge r t with h | h
    · exact h
    · exfalso
      have hle : r ≤ t := Nat.le_of_dvd (by omega) hrt
      have heq : r = t := le_antisymm hle h
      rw [heq] at hr
      exact hnp hr
  -- Step 2 : `t = r * w` with `1 < w`, and `r ∣ c` by Fermat's little theorem
  obtain ⟨w, hw⟩ := hrt
  have hw1 : 1 < w := by
    rcases Nat.lt_or_ge 1 w with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos w with h0 | hp
      · rw [h0, mul_zero] at hw; omega
      · have hw' : w = 1 := by omega
        rw [hw', mul_one] at hw
        omega
  obtain ⟨a2, ha2⟩ := (key r w hr.one_lt hw1 hw).1
  have hpr : (c + 1) ^ r = r * (c * a2) + 1 := by
    rw [p2mX_powEq c r, ha2]; ring
  haveI : Fact r.Prime := ⟨hr⟩
  have hcast : ((c + 1 : ℕ) : ZMod r) = 1 := by
    have h1 : (((c + 1) ^ r : ℕ) : ZMod r) = 1 := by
      rw [hpr]; simp
    rw [Nat.cast_pow, ZMod.pow_card] at h1
    exact h1
  have hrc : r ∣ c := by
    rw [Nat.cast_add, Nat.cast_one] at hcast
    have h3 : ((c : ℕ) : ZMod r) + 1 = 0 + 1 := by rw [zero_add]; exact hcast
    exact (ZMod.natCast_eq_zero_iff c r).mp (add_right_cancel h3)
  -- Step 3 : `r` is odd, so `∑_{j<r} j = r * s`
  have htodd : t % 2 = 1 := Nat.odd_iff.mp hodd
  have hrodd : r % 2 = 1 := by
    rcases Nat.even_or_odd r with he | ho
    · exfalso
      obtain ⟨rr, hrr⟩ := he
      have h2t : (2 : ℕ) ∣ t := ⟨rr * w, by rw [hw, hrr]; ring⟩
      omega
    · exact Nat.odd_iff.mp ho
  obtain ⟨s, hs⟩ : ∃ s, r = 2 * s + 1 := ⟨r / 2, by omega⟩
  have hG : (∑ j ∈ Finset.range r, j) = r * s := by
    have h2 := Finset.sum_range_id_mul_two r
    have h3 : r - 1 = 2 * s := by omega
    rw [h3] at h2
    have h4 : (∑ j ∈ Finset.range r, j) * 2 = (r * s) * 2 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4
  -- Step 4 : the length-`r` block is `r + r*r*(…)`, hence equals `r`; contradiction
  obtain ⟨k, hk⟩ := hrc
  have hCform : (c + 1) ^ w
      = r * (k * (∑ i ∈ Finset.range w, (c + 1) ^ i)) + 1 := by
    rw [p2mX_powEq c w, hk]; ring
  obtain ⟨Z, hZ⟩ := p2mX_geomExpand r (k * (∑ i ∈ Finset.range w, (c + 1) ^ i)) r
  have hDval : (∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j)
      = r + r * r * ((k * (∑ i ∈ Finset.range w, (c + 1) ^ i)) * s + Z) := by
    rw [hCform, hZ, hG]; ring
  have hsplit : (∑ i ∈ Finset.range w, (c + 1) ^ i) *
      (∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j) = r ^ beta := by
    rw [← p2mX_splitSum (c + 1) w r, show w * r = t by rw [hw]; ring]
    exact hgeom'
  have hDdvd : (∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j) ∣ r ^ beta :=
    ⟨∑ i ∈ Finset.range w, (c + 1) ^ i, by rw [← hsplit]; ring⟩
  have hD1 : 1 < ∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j :=
    lt_of_lt_of_le hr.one_lt
      (p2mX_le_geom ((c + 1) ^ w) r (Nat.one_le_pow w (c + 1) (by omega)))
  obtain ⟨γ, _hγle, hγ⟩ := (Nat.dvd_prime_pow hr).mp hDdvd
  have hγ1 : γ = 1 := by
    rcases Nat.lt_or_ge γ 2 with h | h
    · rcases Nat.eq_zero_or_pos γ with h0 | hpos
      · exfalso; rw [h0, pow_zero] at hγ; omega
      · omega
    · exfalso
      have hrr : r * r ∣ (∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j) := by
        rw [hγ]
        have hp2 : r ^ 2 ∣ r ^ γ := pow_dvd_pow r h
        have hsq : r * r = r ^ 2 := by ring
        rw [hsq]
        exact hp2
      rw [hDval] at hrr
      have h1 : r * r ∣ r * r * ((k * (∑ i ∈ Finset.range w, (c + 1) ^ i)) * s + Z) :=
        ⟨(k * (∑ i ∈ Finset.range w, (c + 1) ^ i)) * s + Z, rfl⟩
      have hW : r * r ∣ r := by
        have h2 := Nat.dvd_sub hrr h1
        simpa using h2
      have hle : r * r ≤ r := Nat.le_of_dvd (by omega) hW
      have h6 : 2 * r ≤ r * r := Nat.mul_le_mul hr2 (le_refl r)
      have h7 : 2 * r ≤ r := le_trans h6 hle
      omega
  rw [hγ1, pow_one] at hγ
  have hlt : r < ∑ j ∈ Finset.range r, ((c + 1) ^ w) ^ j :=
    p2mX_lt_geom ((c + 1) ^ w) r (Nat.one_lt_pow (by omega) (by omega)) hr.one_lt
  rw [hγ] at hlt
  exact lt_irrefl r hlt