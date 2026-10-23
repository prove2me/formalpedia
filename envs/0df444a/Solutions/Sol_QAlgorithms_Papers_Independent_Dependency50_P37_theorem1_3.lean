-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:46:45.572183+00:00
-- url     : https://prove2.me/submissions/e88eac40-0dfa-4478-b874-6f17f70a2710

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace X8P37

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P62 (graph)

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem x8_kraus_single {ι : Type} [Fintype ι] (E : ι → Matrix O I ℂ) (x y : I) (a b : O) :
    krausApply E (Matrix.single x y 1) a b = ∑ i, E i a x * conj (E i b y) := by
  simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem x8_dual (f : Matrix O I ℂ →ₗ[ℂ] ℂ) (M : Matrix O I ℂ) :
    f M = ∑ p : O × I, f (Matrix.single p.1 p.2 1) * M p.1 p.2 := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show Matrix.single a x (M a x) = M a x • Matrix.single a x (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

theorem x8_quad {ι : Type} [Fintype ι] (E : ι → Matrix O I ℂ) (f : Matrix O I ℂ →ₗ[ℂ] ℂ) :
    ∑ i, f (E i) * conj (f (E i)) =
      ∑ p : O × I, ∑ q : O × I, f (Matrix.single p.1 p.2 1) *
        conj (f (Matrix.single q.1 q.2 1)) * krausApply E (Matrix.single p.2 q.2 1) p.1 q.1 := by
  simp_rw [x8_kraus_single]
  have : ∀ i, f (E i) * conj (f (E i)) = ∑ p : O × I, ∑ q : O × I,
      f (Matrix.single p.1 p.2 1) * conj (f (Matrix.single q.1 q.2 1)) *
        (E i p.1 p.2 * conj (E i q.1 q.2)) := by
    intro i
    rw [x8_dual f (E i), map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]; ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]

theorem x8_span_le {ι κ : Type} [Fintype ι] [Fintype κ] (E : ι → Matrix O I ℂ)
    (F : κ → Matrix O I ℂ) (h : ∀ ρ, krausApply E ρ = krausApply F ρ) :
    Submodule.span ℂ (Set.range E) ≤ Submodule.span ℂ (Set.range F) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_contra hn
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hF0 : ∀ k, f (F k) = 0 := by
    intro k
    have : f (F k) ∈ (Submodule.span ℂ (Set.range F)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
    rw [hmap] at this
    simpa using this
  have hq := x8_quad F f
  rw [← funext h, ← x8_quad E f] at hq
  simp only [hF0, zero_mul, Finset.sum_const_zero] at hq
  have hn : ∀ z : ℂ, z * conj z = ((Complex.normSq z : ℝ) : ℂ) := fun z => Complex.mul_conj z
  simp_rw [hn] at hq
  rw [← Complex.ofReal_sum, eq_comm, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at hq
  exact hf (Complex.normSq_eq_zero.mp (hq i (Finset.mem_univ _)))

theorem x8_mul_mem {ι : Type} [Fintype ι] (E : ι → Matrix O I ℂ) {A B : Matrix O I ℂ}
    (hA : A ∈ Submodule.span ℂ (Set.range E)) (hB : B ∈ Submodule.span ℂ (Set.range E)) :
    Aᴴ * B ∈ Submodule.span ℂ (Set.range fun p : ι × ι => (E p.1)ᴴ * E p.2) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA
  obtain ⟨e, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hB
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

theorem x8_graph {ι : Type} [Fintype ι] (F : Superop I O) (E : ι → Matrix O I ℂ)
    (hE : IsKrausFamily E) (hF : ∀ R, F R = krausApply E R) :
    graph F = Submodule.span ℂ (Set.range fun p : ι × ι => (E p.1)ᴴ * E p.2) := by
  apply le_antisymm
  · rw [graph, Submodule.span_le]
    rintro X ⟨r, G, -, hFG, i, j, rfl⟩
    have hle := x8_span_le G E (fun ρ => by rw [← hFG, hF])
    exact x8_mul_mem E (hle (Submodule.subset_span ⟨i, rfl⟩))
      (hle (Submodule.subset_span ⟨j, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨Fintype.card ι, E ∘ (Fintype.equivFin ι).symm, ?_, ?_,
      Fintype.equivFin ι i, Fintype.equivFin ι j, by simp⟩
    · unfold IsKrausFamily at hE ⊢
      rw [← hE]
      exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun k => (E k)ᴴ * E k)
    · intro R
      rw [hF]
      unfold krausApply
      exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun k => E k * R * (E k)ᴴ)).symm

/-- the operator-system recursion map -/
def x8T {m : ℕ} (K : Fin m → Matrix I I ℂ) (S : Submodule ℂ (Matrix I I ℂ)) :
    Submodule ℂ (Matrix I I ℂ) :=
  Submodule.span ℂ {Y | ∃ X ∈ S, ∃ i j, Y = (K i)ᴴ * X * K j}

theorem x8T_mono {m : ℕ} (K : Fin m → Matrix I I ℂ) {S S' : Submodule ℂ (Matrix I I ℂ)}
    (h : S ≤ S') : x8T K S ≤ x8T K S' := by
  apply Submodule.span_mono
  rintro _ ⟨X, hX, i, j, rfl⟩
  exact ⟨X, h hX, i, j, rfl⟩

theorem x8T_span {m : ℕ} (K : Fin m → Matrix I I ℂ) (G : Set (Matrix I I ℂ)) :
    x8T K (Submodule.span ℂ G) =
      Submodule.span ℂ {Y | ∃ X ∈ G, ∃ i j, Y = (K i)ᴴ * X * K j} := by
  apply le_antisymm
  · rw [x8T, Submodule.span_le]
    rintro _ ⟨X, hX, i, j, rfl⟩
    induction hX using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, i, j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ _ hx
  · apply Submodule.span_mono
    rintro _ ⟨X, hX, i, j, rfl⟩
    exact ⟨X, Submodule.subset_span hX, i, j, rfl⟩

theorem x8_prod_kraus {r m : ℕ} (E : Fin r → Matrix I I ℂ) (K : Fin m → Matrix I I ℂ)
    (hE : IsKrausFamily E) (hK : IsKrausFamily K) :
    IsKrausFamily (fun p : Fin r × Fin m => E p.1 * K p.2) := by
  unfold IsKrausFamily at hE hK ⊢
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc _ = ∑ i, (K i)ᴴ * (∑ a, (E a)ᴴ * E a) * K i := by
        simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc, Matrix.conjTranspose_mul]
    _ = 1 := by rw [hE]; simpa using hK

theorem x8_prod_apply (Φ : Superop I I) {r m : ℕ} (E : Fin r → Matrix I I ℂ)
    (K : Fin m → Matrix I I ℂ) (hΦ : ∀ ρ, Φ ρ = krausApply K ρ) (n : ℕ)
    (hn : ∀ ρ, Φ^[n] ρ = krausApply E ρ) :
    ∀ ρ, Φ^[n + 1] ρ = krausApply (fun p : Fin r × Fin m => E p.1 * K p.2) ρ := by
  intro ρ
  rw [Function.iterate_succ_apply, hn, hΦ]
  unfold krausApply
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem x8_iter_kraus (Φ : Superop I I) {m : ℕ} (K : Fin m → Matrix I I ℂ)
    (hK : IsKrausFamily K) (hΦ : ∀ ρ, Φ ρ = krausApply K ρ) (n : ℕ) :
    ∃ (r : ℕ) (E : Fin r → Matrix I I ℂ), IsKrausFamily E ∧ ∀ ρ, Φ^[n] ρ = krausApply E ρ := by
  induction n with
  | zero =>
    refine ⟨1, fun _ => 1, ?_, ?_⟩
    · simp [IsKrausFamily]
    · intro ρ; simp [krausApply]
  | succ n ih =>
    obtain ⟨r, E, hE, hn⟩ := ih
    refine ⟨r * m, fun t => E (finProdFinEquiv.symm t).1 * K (finProdFinEquiv.symm t).2, ?_, ?_⟩
    · have := x8_prod_kraus E K hE hK
      unfold IsKrausFamily at this ⊢
      rw [← this]
      exact Equiv.sum_comp finProdFinEquiv.symm
        (fun p : Fin r × Fin m => (E p.1 * K p.2)ᴴ * (E p.1 * K p.2))
    · intro ρ
      rw [x8_prod_apply Φ E K hΦ n hn]
      unfold krausApply
      exact (Equiv.sum_comp finProdFinEquiv.symm
        (fun p : Fin r × Fin m => (E p.1 * K p.2) * ρ * (E p.1 * K p.2)ᴴ)).symm

theorem x8_rec (Φ : Superop I I) {m : ℕ} (K : Fin m → Matrix I I ℂ)
    (hK : IsKrausFamily K) (hΦ : ∀ ρ, Φ ρ = krausApply K ρ) (n : ℕ) :
    graph (Φ^[n + 1]) = x8T K (graph (Φ^[n])) := by
  obtain ⟨r, E, hE, hn⟩ := x8_iter_kraus Φ K hK hΦ n
  have hG := x8_prod_kraus E K hE hK
  have hGn := x8_prod_apply Φ E K hΦ n hn
  rw [x8_graph _ _ hG hGn, x8_graph _ _ hE hn, x8T_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, rfl⟩
    exact Submodule.subset_span ⟨(E a)ᴴ * E b, ⟨(a, b), rfl⟩, i, j, by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, i, j, rfl⟩
    exact Submodule.subset_span ⟨((a, i), (b, j)), by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩

theorem x8_one_mem {m : ℕ} (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) :
    (1 : Matrix I I ℂ) ∈ Submodule.span ℂ (Set.range fun p : Fin m × Fin m => (K p.1)ᴴ * K p.2) := by
  rw [← hK]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨(i, i), rfl⟩

theorem x8_main (Φ : Superop I I) (hΦc : IsChannel Φ) [Nonempty I] :
    (∀ n : ℕ, 0 < n → graph (Φ^[n]) ≤ graph (Φ^[n + 1])) ∧
    ∃ N : ℕ, 0 < N ∧ N ≤ Fintype.card I ^ 2 ∧
      N ≤ Fintype.card I ^ 2 - Module.finrank ℂ (graph Φ) + 1 ∧
      (∀ n : ℕ, 0 < n → n < N → graph (Φ^[n]) < graph (Φ^[n + 1])) ∧
      ∀ n : ℕ, graph (Φ^[N]) = graph (Φ^[N + n]) := by
  obtain ⟨m, K, hK, hΦ⟩ := hΦc
  set S : ℕ → Submodule ℂ (Matrix I I ℂ) := fun n => graph (Φ^[n]) with hS
  have hrec : ∀ n, S (n + 1) = x8T K (S n) := fun n => x8_rec Φ K hK hΦ n
  have hS1 : S 1 = Submodule.span ℂ (Set.range fun p : Fin m × Fin m => (K p.1)ᴴ * K p.2) :=
    x8_graph _ K hK (by simpa using hΦ)
  have h1 : (1 : Matrix I I ℂ) ∈ S 1 := hS1 ▸ x8_one_mem K hK
  have hmono : ∀ n, 0 < n → S n ≤ S (n + 1) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [hrec 1]
        conv_lhs => rw [hS1]
        rw [Submodule.span_le]
        rintro _ ⟨⟨i, j⟩, rfl⟩
        exact Submodule.subset_span ⟨1, h1, i, j, by simp⟩
      · rw [hrec (n + 1)]
        conv_lhs => rw [hrec n]
        exact x8T_mono K (ih hpos)
  have hstab : ∀ N, S N = S (N + 1) → ∀ k, S N = S (N + k) := by
    intro N hN k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, hrec (N + k), ← ih, ← hrec, ← hN]
  have hD : ∀ n, Module.finrank ℂ (S n) ≤ Fintype.card I ^ 2 := by
    intro n
    calc Module.finrank ℂ (S n) ≤ Module.finrank ℂ (Matrix I I ℂ) := Submodule.finrank_le _
      _ = Fintype.card I ^ 2 := by simp [Module.finrank_matrix, sq]
  have hf1 : 1 ≤ Module.finrank ℂ (S 1) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have : (1 : Matrix I I ℂ) ∈ (⊥ : Submodule ℂ (Matrix I I ℂ)) := h0 ▸ h1
    exact one_ne_zero ((Submodule.mem_bot ℂ).mp this)
  have hex : ∃ n, 1 ≤ n ∧ S n = S (n + 1) := by
    by_contra hne
    push Not at hne
    have hgrow : ∀ n, 1 ≤ n → n ≤ Module.finrank ℂ (S n) := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simpa using hf1
        · have hlt : S n < S (n + 1) := lt_of_le_of_ne (hmono n hpos) (hne n hpos)
          have := Submodule.finrank_lt_finrank_of_lt hlt
          have := ih hpos
          omega
    have := hgrow (Fintype.card I ^ 2 + 1) (by omega)
    have := hD (Fintype.card I ^ 2 + 1)
    omega
  classical
  let N := Nat.find hex
  have hNspec : 1 ≤ N ∧ S N = S (N + 1) := Nat.find_spec hex
  have hlt : ∀ n, 0 < n → n < N → S n < S (n + 1) := by
    intro n hn hnN
    refine lt_of_le_of_ne (hmono n hn) fun h => ?_
    exact Nat.find_min hex hnN ⟨hn, h⟩
  have hlow : ∀ k, 1 ≤ k → k ≤ N → Module.finrank ℂ (S 1) + (k - 1) ≤ Module.finrank ℂ (S k) := by
    intro k hk hkN
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp
      · have := Submodule.finrank_lt_finrank_of_lt (hlt k hpos (by omega))
        have := ih hpos (by omega)
        omega
  have hb := hlow N hNspec.1 le_rfl
  have hDN := hD N
  refine ⟨fun n hn => hmono n hn, N, hNspec.1, by omega, ?_, hlt, hstab N hNspec.2⟩
  have : S 1 = graph Φ := by simp [hS]
  rw [← this]
  omega

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

theorem x8_stab_cap {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 ∧ N ≤ d ^ 2 - Module.finrank ℂ (graph Phi) + 1 ∧
      ∀ n : ℕ,
        quantumCapacity (Nat.iterate Phi N) = quantumCapacity (Nat.iterate Phi (N + n)) ∧
        classicalCapacity (Nat.iterate Phi N) = classicalCapacity (Nat.iterate Phi (N + n)) ∧
        assistedCapacity (Nat.iterate Phi N) = assistedCapacity (Nat.iterate Phi (N + n)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨-, N, hN0, hNd, hNb, -, hst⟩ := x8_main Phi hPhi
  simp only [Fintype.card_fin] at hNd hNb
  refine ⟨N, hN0, hNd, hNb, fun n => ?_⟩
  have h := hst n
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [quantumCapacity, classicalCapacity, assistedCapacity]
    rw [h]

end X8P37


open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37 in
open QAlgorithms.Papers.Independent.Information100.P62 (classicalCapacity assistedCapacity quantumCapacity graph) in
theorem solution {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (h : EventuallyQuantumScrambling Phi) : quantumTime Phi ≤ (d ^ 2 : ℕ) := by
  obtain ⟨n, hn0, hn⟩ := h
  obtain ⟨N, hN0, hNd, -, hst⟩ := X8P37.x8_stab_cap hd Phi hPhi
  have hle : ∀ k : ℕ, 0 < k → quantumCapacity (Nat.iterate Phi k) = 0 →
      quantumTime Phi ≤ (k : WithTop ℕ) := fun k hk hq =>
    sInf_le ⟨k, ⟨hk, hq⟩, rfl⟩
  by_cases hnN : n ≤ N
  · exact (hle n hn0 hn).trans (WithTop.coe_le_coe.mpr (hnN.trans hNd))
  · have hQ : quantumCapacity (Nat.iterate Phi N) = 0 := by
      rw [(hst (n - N)).1, Nat.add_sub_cancel' (by omega)]; exact hn
    exact (hle N hN0 hQ).trans (WithTop.coe_le_coe.mpr hNd)
